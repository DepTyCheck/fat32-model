#!/bin/bash

set -e

if [ $# -lt 2 ]; then
    die "not enough arguments. usage: $0 <dir>"
fi

TMPDIR=$(mktemp -d)
MOUNTPOINT=/mnt
LOOPDEVICE=/dev/loop0

for f in "$1"/*.img; do
    gcc -Wall -Wextra -pedantic --std=gnu99 "${f%.img}.c" -o "${f%.img}.test" 2>&1 | tee -a "${f%.img}.log"
    cp -f "$f" "$TMPDIR/curr.img"
    losetup $LOOPDEVICE "$TMPDIR/curr.img" 2>&1 | tee -a "${f%.img}.log"
    echo 1 > /sys/kernel/debug/llvm-cov/reset
    mount $LOOPDEVICE $MOUNTPOINT 2>&1 | tee -a "${f%.img}.log"
    "${f%.img}.test" $MOUNTPOINT 2>&1 | tee -a "${f%.img}.log"
    umount $MOUNTPOINT 2>&1 | tee -a "${f%.img}.log"
    cp /sys/kernel/debug/llvm-cov/profraw "${f%.img}.profraw"
    losetup -d $LOOPDEVICE 2>&1 | tee -a "${f%.img}.log"
done
