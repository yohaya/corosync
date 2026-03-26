# Building the Debian Package for Proxmox 9.1

## Prerequisites (run on Debian 12/13 or Proxmox host)

```bash
apt-get install -y \
  build-essential devscripts debhelper-compat \
  autoconf automake libtool pkg-config \
  libqb-dev libknet1-dev zlib1g-dev \
  groff docbook2x libxml2-utils xsltproc
```

## Build steps

```bash
# 1. Clone the fork
git clone https://github.com/yohaya/corosync -b stability-fixes /tmp/corosync-build
cd /tmp/corosync-build

# 2. Generate configure script
./autogen.sh

# 3. Build the Debian packages (no signing required)
dpkg-buildpackage -b -uc -us -j$(nproc)

# 4. Packages will be in /tmp/
ls /tmp/*.deb
```

## Install on Proxmox

```bash
# Stop corosync first (if running)
systemctl stop corosync corosync-qdevice 2>/dev/null

# Install packages
dpkg -i /tmp/corosync_3.1.10-pve1_amd64.deb \
        /tmp/libcorosync-common4_3.1.10-pve1_amd64.deb \
        /tmp/corosync-qdevice_3.1.10-pve1_amd64.deb

# Fix any dependency issues
apt-get install -f

# Restart
systemctl start corosync
```

## What's fixed in this build

| Bug | File | Impact |
|-----|------|--------|
| 13 assert() crashes | exec/totemsrp.c | Daemon restart storm on CPG failure |
| retrans_queue TODO LEAK | exec/totemsrp.c | ~1 GB per ring-recovery event |
| assembly_list_free unbounded | exec/totempg.c | 15+ GiB RSS on 53-node cluster |
| alloca() stack overflow | exec/cpg.c | Stack corruption with 100+ members |
| Dead write | exec/totemudp.c | Static analysis warning |
| Unsigned -1 return | exec/logsys.c | Silent subsystem lookup failure |
| DIAG logging (6 probes) | exec/totemsrp.c | Token timing, ARU stall, queue pressure |

## Verifying DIAG logs in production

After deployment, these log lines will appear in `/var/log/corosync/corosync.log`:

```
DIAG ring recovery start: reason=4(CONSENSUS_TIMEOUT_EXPIRED) members=53 ...
DIAG ARU stall: node 192.168.1.5 holding group ARU ... for 25 consecutive passes
DIAG write throttled: FCC limit hit (10 consecutive passes), 847 msgs queued
DIAG ring recovery complete in 4231 ms (peak_retrans_hwm=2847)
```

A `peak_retrans_hwm` value above 12000 (73% of the 16384 limit) means you
were close to the crash boundary that this build eliminates.
