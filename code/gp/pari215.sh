#!/bin/sh
# The PARI/GP checks under PARI/GP 2.15.4, the version installed by the gp job of the continuous
# integration (the pari-gp package of Ubuntu 24.04), while the recorded outputs were made with PARI/GP
# 2.17.4: the twelve checks of that job run with code/rerun.sh in a container of Ubuntu 24.04 (the image
# sagemath/sagemath:10.9, with /usr/bin/gp of the package, not the PARI of Sage), on a copy of code/ and
# data/. Prints the system, the package, the version and one result line per check.
# Usage (from the repository root, with docker, or DOCKER=podman): code/gp/pari215.sh
set -eu
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
cp -r code data "$W/"
cat > "$W/run.sh" <<'IN'
set -u
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq > /dev/null && apt-get install -y -qq pari-gp > /dev/null 2>&1
cd /w
export PATH=/usr/bin:/bin
. /etc/os-release; echo "system: $PRETTY_NAME"
echo "package: $(dpkg-query -W -f='${Package} ${Version}' pari-gp)"
echo 'print("PARI/GP ", version())' | gp -q
code/rerun.sh paper_checks structure_checks rtrig_consts consts120 params bk15_c3_coords tie_targets_check \
  kappa_gale kappa_vertex local_nonlinear contact_graphs consts_check | sed 's/ ([0-9]* s)$//'
IN
${DOCKER:-docker} run --rm --user root -v "$W:/w" sagemath/sagemath:10.9 bash /w/run.sh
