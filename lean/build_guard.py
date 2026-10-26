"""Authorized local completion: one supervised process group, aggregate 6 GiB.

Copied from the reviewed recovery guard. All compiler children must inherit the
coordinator process group; no inner child may create a new session. Host pressure,
identity-safe cleanup, staging, disk and log protections remain unchanged.
Explicit long stage deadlines are capped at 10800 seconds; default remains120s.
"""
from contextlib import contextmanager
from functools import wraps
from pathlib import Path
import fcntl
import hashlib
import importlib.util
import json
import os
import re
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
MIN_FREE_BYTES = 15 * 1024**3


def require_free_disk(path):
    import shutil
    path = Path(path)
    while not path.exists():
        path = path.parent
    free = shutil.disk_usage(path).free
    if free < MIN_FREE_BYTES:
        raise RuntimeError('Fewer than 15 GiB free disk space; no compilation started')
    return free


def layout():
    from build import workspace
    return {'workspace': workspace()}


LEAN_MEMORY_MIB = 4096
RSS_LIMIT_KIB = 6 * 1024 * 1024
TIMEOUT_SECONDS = 120
MAX_TIMEOUT_SECONDS = 10800
LOG_LIMIT_BYTES = 4 * 1024 * 1024
POLL_SECONDS = 1
HOST_PROBE_TIMEOUT_SECONDS = 2
HOST_NORMAL_PRESSURE_LEVEL = 1
MIN_HOST_REPORTED_FREE_PERCENT = 25
_slot_fd = None


def host_memory_snapshot():
    """Read host signals; missing, malformed or timed-out probes fail closed."""
    pressure = subprocess.run(
        ['/usr/sbin/sysctl', '-n', 'kern.memorystatus_vm_pressure_level'],
        capture_output=True, text=True, check=True,
        timeout=HOST_PROBE_TIMEOUT_SECONDS).stdout.strip()
    if not re.fullmatch(r'[0-9]+', pressure):
        raise RuntimeError('Cannot parse host memory-pressure level')
    free = subprocess.run(['/usr/bin/memory_pressure', '-Q'],
        capture_output=True, text=True, check=True,
        timeout=HOST_PROBE_TIMEOUT_SECONDS).stdout
    matches = re.findall(r'^System-wide memory free percentage:\s*([0-9]+)%\s*$',
                         free, flags=re.MULTILINE)
    if len(matches) != 1 or not 0 <= int(matches[0]) <= 100:
        raise RuntimeError('Cannot parse host reported free-memory percentage')
    return {'pressure_level': int(pressure), 'reported_free_percent': int(matches[0])}


def host_stop_reason(snapshot):
    if set(snapshot) != {'pressure_level', 'reported_free_percent'} or any(
            type(snapshot[key]) is not int for key in snapshot):
        raise RuntimeError('Invalid host memory snapshot')
    if not 0 <= snapshot['reported_free_percent'] <= 100:
        raise RuntimeError('Invalid host reported free-memory percentage')
    if snapshot['pressure_level'] != HOST_NORMAL_PRESSURE_LEVEL:
        return ('Host memory-pressure level is not the required normal value '
                f'{HOST_NORMAL_PRESSURE_LEVEL}: {snapshot["pressure_level"]}')
    if snapshot['reported_free_percent'] < MIN_HOST_REPORTED_FREE_PERCENT:
        return ('Host reported free-memory percentage fell below '
                f'{MIN_HOST_REPORTED_FREE_PERCENT}%: {snapshot["reported_free_percent"]}%')
    return None


@contextmanager
def staged_outputs(output):
    """A stopped check cannot overwrite an existing checked object."""
    output = Path(output)
    with tempfile.TemporaryDirectory(prefix='.lean-check-', dir=output.parent) as tmp:
        staged = Path(tmp) / output.name
        def publish():
            if not staged.is_file():
                raise RuntimeError('Compiler reported success without its object file')
            for path in Path(tmp).iterdir():
                if not path.name.startswith(output.stem + '.') or not path.is_file():
                    raise RuntimeError('Unexpected compiler output: ' + str(path))
            marker = output.with_suffix('.publishing.json')
            marker.write_text(json.dumps({'status': 'INCOMPLETE_PUBLICATION',
                                          'runner_pid': os.getpid()}))
            output.with_suffix('.build.json').unlink(missing_ok=True)
            for path in Path(tmp).iterdir():
                os.replace(path, output.parent / path.name)
            marker.unlink()
        yield staged, publish


@contextmanager
def compiler_slot(lock_path, *, wait_seconds=0):
    """The child inherits this flock, retaining it if the wrapper is killed."""
    global _slot_fd
    if _slot_fd is not None:
        raise RuntimeError('Nested compiler slots are not supported')
    lock_path = Path(lock_path)
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
    try:
        deadline = time.monotonic() + wait_seconds
        next_notice = 0
        while True:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                now = time.monotonic()
                if now >= deadline:
                    raise RuntimeError('Another proof runner holds this project\'s compiler slot; no job started')
                if now >= next_notice:
                    print('Waiting for this project\'s compiler slot; no compiler started.', flush=True)
                    next_notice = now + 30
                time.sleep(min(2, deadline - now))
        os.ftruncate(fd, 0)
        os.write(fd, json.dumps({'runner_pid': os.getpid(), 'policy': 'one supervised job per project'}).encode())
        _slot_fd = fd
        yield
    finally:
        _slot_fd = None
        # Do not unlink the lock or explicitly unlock an FD inherited by a child.
        os.close(fd)


def serialized(main):
    @wraps(main)
    def guarded(*args, **kwargs):
        loc = layout()
        # Serialize this project's staging and outputs across agents and pins.
        # Ordinary checks only read the shared, pinned dependencies; they must
        # not reserve the machine-wide dependency-installation lock.
        with compiler_slot(loc['workspace'].parent / 'compile.lock', wait_seconds=1800):
            return main(*args, **kwargs)
    return guarded


def group_rss_kib(pgid):
    result = subprocess.run(['/bin/ps', '-axo', 'pgid=,rss='],
        capture_output=True, text=True, check=True, timeout=2)
    total = 0
    for line in result.stdout.splitlines():
        group, rss = map(int, line.split())
        if group == pgid:
            total += rss
    return total


def group_members(pgid, *, pid=None):
    """Inspect exact group membership, including UID, state, and start-time identity."""
    select = ['-p', str(pid)] if pid is not None else ['-ax']
    result = subprocess.run(['/bin/ps', *select, '-o', 'pid=,pgid=,uid=,stat=,lstart='],
        capture_output=True, text=True, timeout=2)
    if result.returncode == 1 and not result.stdout.strip() and not result.stderr.strip():
        return []  # A selected PID disappeared before ps inspected it.
    result.check_returncode()
    members = []
    for line in result.stdout.splitlines():
        fields = line.split(None, 4)
        if len(fields) != 5:
            raise RuntimeError('Cannot safely parse process membership: ' + repr(line))
        member_pid, group, uid = map(int, fields[:3])
        if group == pgid:
            members.append({'pid': member_pid, 'pgid': group, 'uid': uid,
                            'state': fields[3], 'started': fields[4]})
    return members


def process_identity(member):
    return tuple(member[key] for key in ('pid', 'pgid', 'uid', 'started'))


def kill_group(pgid, *, expected_leader=None):
    """Stop only a caller-owned new-session group; verify that no live member remains.

    macOS can deny killpg after a group has already disappeared. On denial, inspect
    the group and use positive-PID SIGKILL only for reidentified current-user members.
    Zombies need no signal. PID identity changes or persistent live members fail closed.
    """
    if not isinstance(pgid, int) or pgid <= 1 or pgid == os.getpgrp():
        raise RuntimeError('Refusing unsafe process-group cleanup target')
    current_uid = os.geteuid()
    identities = {}
    signaled = []
    method = 'already-inactive'

    def snapshot():
        members = group_members(pgid)
        for member in members:
            identity = process_identity(member)
            if member['pid'] == pgid and expected_leader is not None and identity != expected_leader:
                raise RuntimeError('Process-group leader identity changed; refusing further cleanup signals')
            previous = identities.setdefault(member['pid'], identity)
            if previous != identity:
                raise RuntimeError('Process identity changed during cleanup; refusing to signal it')
        return members

    def live(members):
        return [member for member in members if not member['state'].startswith('Z')]

    members = snapshot()
    if not live(members):
        return {'pgid': pgid, 'method': method, 'signaled_pids': [], 'result': 'no-live-members'}
    if all(member['uid'] == current_uid for member in members):
        try:
            os.killpg(pgid, signal.SIGKILL)
            method = 'group-sigkill'
        except ProcessLookupError:
            method = 'group-disappeared'
        except PermissionError:
            method = 'permission-fallback-positive-pids'
    else:
        # Do not send even a group signal if another UID is present.
        method = 'mixed-uid-positive-pids-only'

    deadline = time.monotonic() + 2  # Bounded shutdown observation, not extra check time.
    while True:
        members = live(snapshot())
        if not members:
            return {'pgid': pgid, 'method': method,
                    'signaled_pids': sorted(set(signaled)), 'result': 'no-live-members'}
        for member in members:
            if member['uid'] != current_uid:
                continue
            current = group_members(pgid, pid=member['pid'])
            if not current or not live(current):
                continue
            if len(current) != 1 or process_identity(current[0]) != process_identity(member):
                raise RuntimeError('Process identity changed before cleanup signal; refusing to signal it')
            try:
                # Recheck the group and its original new-session boundary immediately before kill.
                if os.getpgid(member['pid']) != pgid or os.getsid(member['pid']) != pgid:
                    raise RuntimeError('Process left the owned group/session before cleanup signal')
                os.kill(member['pid'], signal.SIGKILL)
                signaled.append(member['pid'])
            except ProcessLookupError:
                pass
            except PermissionError:
                pass  # It may have vanished; the mandatory liveness check below decides.
        if time.monotonic() >= deadline:
            remaining = live(snapshot())
            if remaining:
                detail = [(m['pid'], m['uid'], m['state']) for m in remaining]
                raise RuntimeError(f'Unable to stop owned process group {pgid}; live (pid, uid, state): {detail}')
        time.sleep(0.05)


def run_checked(cmd, *, cwd, env, log_path, timeout_seconds=None):
    if timeout_seconds is None:
        timeout_seconds = TIMEOUT_SECONDS
    if type(timeout_seconds) is not int or not 1 <= timeout_seconds <= MAX_TIMEOUT_SECONDS:
        raise ValueError(f'Check timeout must be an integer from 1 to {MAX_TIMEOUT_SECONDS} seconds')
    if _slot_fd is None:
        raise RuntimeError('Compilation requires this project\'s compiler slot')
    require_free_disk(cwd)
    log_path = Path(log_path)
    started = time.monotonic()
    reason = None
    peak = 0
    proc = None
    previous_handlers = {}
    leader_identity = None
    cleanup_events = []
    host = {'attempted_samples': 0, 'successful_samples': 0, 'initial': None,
            'last': None, 'minimum_reported_free_percent': None,
            'maximum_pressure_level_observed': None}

    def observe_host():
        host['attempted_samples'] += 1
        try:
            snapshot = host_memory_snapshot()
            stop = host_stop_reason(snapshot)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            return f'Host memory monitor failed; no further checking allowed: {error}'
        host['successful_samples'] += 1
        if host['initial'] is None:
            host['initial'] = dict(snapshot)
        host['last'] = dict(snapshot)
        minimum = host['minimum_reported_free_percent']
        maximum = host['maximum_pressure_level_observed']
        host['minimum_reported_free_percent'] = (snapshot['reported_free_percent']
            if minimum is None else min(minimum, snapshot['reported_free_percent']))
        host['maximum_pressure_level_observed'] = (snapshot['pressure_level']
            if maximum is None else max(maximum, snapshot['pressure_level']))
        return stop

    def cleanup():
        cleanup_events.append(kill_group(proc.pid, expected_leader=leader_identity))

    def interrupted(signum, _frame):
        raise KeyboardInterrupt(f'Runner interrupted by signal {signum}')

    try:
        for sig in (signal.SIGINT, signal.SIGTERM):
            previous_handlers[sig] = signal.signal(sig, interrupted)
        with log_path.open('w') as log:
            reason = observe_host()
            if reason is None:
                proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=log,
                    stderr=subprocess.STDOUT, start_new_session=True,
                    pass_fds=(_slot_fd,))
                # Capture the unreaped child leader before poll/wait can release its PID.
                leader = group_members(proc.pid, pid=proc.pid)
                if len(leader) != 1 or leader[0]['uid'] != os.geteuid():
                    raise RuntimeError('Cannot identify the owned process-group leader safely')
                leader_identity = process_identity(leader[0])
                while proc.poll() is None:
                    try:
                        peak = max(peak, group_rss_kib(proc.pid))
                    except (OSError, ValueError, subprocess.SubprocessError) as error:
                        reason = f'Resource monitor failed; stopped safely: {error}'
                        break
                    if peak > RSS_LIMIT_KIB:
                        reason = 'Process-group RSS exceeded the 6 GiB aggregate sampled watchdog threshold'
                        break
                    reason = observe_host()
                    if reason:
                        break
                    if time.monotonic() - started > timeout_seconds:
                        reason = f'Check exceeded the {timeout_seconds}-second batch deadline'
                        break
                    if log_path.stat().st_size > LOG_LIMIT_BYTES:
                        reason = 'Check exceeded the bounded diagnostic-log size'
                        break
                    time.sleep(POLL_SECONDS)
                if reason:
                    cleanup()
                proc.wait()
    except KeyboardInterrupt:
        reason = 'Check interrupted; process group stopped and existing objects preserved'
        if proc is not None:
            cleanup()
            proc.wait()
    except BaseException:
        if proc is not None:
            cleanup()
            proc.wait()
        raise
    finally:
        try:
            if proc is not None:
                # Also remove descendants if the main child exited unexpectedly.
                cleanup()
        finally:
            for sig, handler in previous_handlers.items():
                signal.signal(sig, handler)
    # A child can finish between polls. Natural exit does not excuse a missed
    # deadline or oversized log; cleanup has already verified the owned group.
    elapsed = time.monotonic() - started
    if reason is None:
        if elapsed > timeout_seconds:
            reason = f'Check exceeded the {timeout_seconds}-second batch deadline (final check)'
        elif log_path.stat().st_size > LOG_LIMIT_BYTES:
            reason = 'Check exceeded the bounded diagnostic-log size (final check)'
    if reason:
        with log_path.open('a') as log:
            log.write('\nRESOURCE GUARD: ' + reason + '\nNo retry was started.\n')
    with log_path.open() as log:
        output = log.read(LOG_LIMIT_BYTES + 1024)
    result = subprocess.CompletedProcess(cmd, 125 if reason else proc.returncode, output)
    result.resource_report = {
        'policy': f'completion-owned-group-aggregate-6GiB-sampled-RSS-host-normal-free25pct-{timeout_seconds}s',
        'launched': proc is not None,
        'rss_limit_kib': RSS_LIMIT_KIB,
        'recommended_lean_memory_mib': LEAN_MEMORY_MIB,
        'timeout_limit_seconds': timeout_seconds,
        'poll_sleep_seconds': POLL_SECONDS,
        'host_probe_timeout_seconds': HOST_PROBE_TIMEOUT_SECONDS,
        'required_host_pressure_level': HOST_NORMAL_PRESSURE_LEVEL,
        'minimum_host_reported_free_percent': MIN_HOST_REPORTED_FREE_PERCENT,
        'host_memory': host,
        'limitations': 'Sampled process RSS and host signals; not an OS hard memory cap or control of other jobs.',
        'peak_sampled_rss_kib': peak, 'seconds': round(elapsed, 3),
        'stop_reason': reason, 'cleanup': cleanup_events,
    }
    return result
