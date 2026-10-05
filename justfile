default:
    @just --list

build:
    zig build -Doptimize=ReleaseSafe

test:
    zig build test

# Every fixture in build.zig is its own object step, and an object step is its
# own `zig build-exe --listen=-` compiler *process*. The build runner runs those
# in a `std.Thread.Pool` whose size `-j` sets, defaulting to the CPU count, so an
# unbounded run on this 57-core host asks for 57 live compiler processes at once.
# Nothing else bounds them: the runner's `--maxrss` budget only counts steps
# whose build script declares `max_rss`, and `b.addObject` declares none, so for
# this graph the fixture sweep is limited by `-j` alone.
#
# Past that cliff the workers are killed mid-write, and the failure the gate
# reports says nothing about the fixtures. The runner writes the server protocol
# into each child's stdin (Step.zig `zigProcessUpdate`) and only calls `wait`
# afterwards (`evalZigProcess`), so when the child is already gone that write
# fails first and the step dies with a bare `error: BrokenPipe` - the error
# bundle that would name the offending file never arrives. One run of this gate
# lost nine workers this way across directories that had compiled moments
# earlier, and printed no diagnostic for any of them.
#
# So cap the pool at what the host can serve instead of at what it can count.
# ZWANGIG_BUILD_JOBS pins the bound outright; CI sets it so the workflow does
# not inherit the runner's core count. This is a bound, not a retry: a fixture
# that genuinely fails to compile still fails this gate, once, loudly.
check-fixtures:
    #!/usr/bin/env bash
    set -euo pipefail

    # The build runner parses `-j` only in attached form (`-j8`, not `-j 8`).
    jobs="${ZWANGIG_BUILD_JOBS:-}"
    if [ -n "$jobs" ]; then
        case "$jobs" in
            *[!0-9]*)
                echo "ZWANGIG_BUILD_JOBS must be a positive integer, got '$jobs'" >&2
                exit 2
                ;;
        esac
    else
        cpus="$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)"
        jobs="$cpus"
        if [ "$jobs" -gt 16 ]; then
            jobs=16
        fi
    fi
    if [ "$jobs" -lt 1 ]; then
        jobs=1
    fi

    echo "check-fixtures: compiling fixtures with -j$jobs"
    zig build check-fixtures "-j$jobs"

run:
    zig build run -Doptimize=ReleaseSafe

run-release:
    zig build run -Doptimize=ReleaseFast

fmt:
    #!/usr/bin/env bash
    set -euo pipefail

    zig_version="$(zig version)"
    if [ "$zig_version" != "0.15.2" ]; then
        echo "zig fmt is canonical under Zig 0.15.2; use 'nix develop .#zig015 -c just fmt'" >&2
        exit 1
    fi
    zig fmt src

lint:
    #!/usr/bin/env bash
    set -euo pipefail
    shopt -s globstar

    if [ -f validate.sh ]; then
        shellcheck validate.sh
    fi
    shellcheck scripts/*.sh
    ./scripts/check-doc-versions.sh

    zig_version="$(zig version)"
    case "$zig_version" in
        0.15.2)
            zig fmt --check src/
            ;;
        0.16.0)
            ;;
        *)
            echo "unsupported Zig formatter version: $zig_version" >&2
            exit 1
            ;;
    esac

    if [ -n "${CI:-}" ]; then
        zig build run -Doptimize=ReleaseSafe -- --threads 1 --use-widening --format sarif src/**/*.zig > results.sarif
    else
        zig build run -Doptimize=ReleaseSafe -- --threads 1 --use-widening src/**/*.zig
    fi

validate:
    ./validate.sh

# `build` compiles the analyzer, `test` exercises its behavior, and `lint`
# checks sources and scripts. Compiling the fixtures is its own recipe because
# it is the only gate that proves the test data still builds.
ci: build test lint check-fixtures

release-check TAG:
    ./scripts/release-check.sh {{TAG}}
