#!/bin/bash

set -e

die() { echo "$*" 1>&2 ; exit 1; }

if [ $# -lt 1 ]; then
    die "not enough arguments. usage: $0 <dir>"
fi

TMPDIR=$(mktemp -d)
MOUNTPOINT=/mnt
LOOPDEVICE=/dev/loop0
    
echo "Resetting llvm-cov..."
echo 1 > /sys/kernel/debug/llvm-cov/reset

for f in "$1"/*.img; do {
    echo "Tesing $f..."
    echo "Compiling..."
    gcc -Wall --std=gnu99 "${f%.img}.c" -o "${f%.img}.test"
    echo "Copying image..."
    cp -f "$f" "$TMPDIR/curr.img"
    echo "Setting up loop device..."
    losetup $LOOPDEVICE "$TMPDIR/curr.img"
    echo "Mounting..."
    mount -t msdos $LOOPDEVICE $MOUNTPOINT
    echo "Testing..."
    setpriv --bounding-set '-dac_override' "${f%.img}.test" $MOUNTPOINT
    echo "Unmounting..."
    umount $MOUNTPOINT
    echo "Resetting loop device..."
    losetup -d $LOOPDEVICE
    echo "$f done!"
} 2>&1 | tee -a "${f%.img}.log"
done

# echo "Collecting coverage info..."
# cp /sys/kernel/debug/llvm-cov/profraw "${f%.img}.profraw"
