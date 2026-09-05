#!/bin/bash
cd "$(dirname "$0")"
for t in v0 v3 v4; do echo "### bench $t  $(uptime | sed 's/.*load/load/')"; ./bench_$t 21 all; done
for t in v0 v3 v4; do echo "### harness $t  $(uptime | sed 's/.*load/load/')"; (cd hrepo_$t/adversarial && ./speed 5 0.5 run ChainHash 2>/dev/null); done
echo "### done $(uptime | sed 's/.*load/load/')"
