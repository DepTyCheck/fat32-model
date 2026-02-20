module Filesystems.FAT32.NodeOps.CPrinter

import Filesystems.FAT32
import Filesystems.FAT32.Index
import Filesystems.FAT32.NodeOps

%default total
%hide Data.Nat.divCeilNZ
%prefix_record_projections off

header : Nat -> String
header len = #"""
#define _GNU_SOURCE
#define _XOPEN_SOURCE 500

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <ftw.h>
#include <linux/msdos_fs.h>

#define panic_on(EXPR) do {if (EXPR) {perror(""); assert(0);}} while (0)
#define NFTW_FD_LIMIT 64

int ftw_rm_lambda(const char *fpath, const struct stat *st, int info, struct FTW *offs) {
  return remove(fpath);
}

int rm(const char *path) {
  return nftw(path, ftw_rm_lambda, NFTW_FD_LIMIT, FTW_DEPTH | FTW_PHYS);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "Usage: ");
    fprintf(stderr, "%s", argv[0]);
    fprintf(stderr, " <mount_path>\n");
    exit(EXIT_FAILURE);
  }
  int rootfd = open(argv[1], O_PATH | O_DIRECTORY);
  panic_on(rootfd < 0);
  puts("Running \#{show len} tests...");

"""#

footer : String
footer = #"""
  int gres = close(rootfd);
  panic_on(gres < 0);
}

"""#


public export
index2UnixPath : (node : Node cfg ar fs) -> (idx : IndexIn node rootl dirl) -> String

index2UnixPath' : (sx : HSnocVectMaybeNode cfg k ars prs) -> (names : UniqNames prs) -> (idx : IndexIn sx dirl) -> String 
index2UnixPath' (_ :< Just x) (NewName ff $ Just y) (Here idx) = "\{y}\{index2UnixPath x idx}"
index2UnixPath' (sx :< x) (NewName ff f) (There idx) = index2UnixPath' sx ff idx

index2UnixPath .(Root _ _ @{_}) HereRoot = "./"
index2UnixPath (Root {ars}sx names) (ThereRoot idx) {ar=MkNodeArgs _ (_ + totsum ars)} = "./\{index2UnixPath' sx names idx}"
index2UnixPath (Dir {ars} _ sx names) (ThereDir idx) {ar=MkNodeArgs _ (_ + totsum ars)} = "/\{index2UnixPath' sx names idx}"
index2UnixPath .(File _ _ @{_}) HereFile = ""
index2UnixPath .(Dir _ _ _ @{_}) HereDir = "/"
index2UnixPath .(File _ _ @{_}) (ThereDir _) impossible

public export
shallowIndex2Name : (vect : HSnocVectMaybeNode cfg k ars prs) -> (ff : UniqNames prs) -> (sidx : ShallowIndexIn vect) -> String
shallowIndex2Name (xs :< Just x) (NewName ff (Just f)) SHere = "\{f}"
shallowIndex2Name (xs :< x) (NewName ff f) (SThere idx) = shallowIndex2Name xs ff idx

public export
indexPair2Name : (node : Node cfg ar Rootful) -> (idx : IndexIn node rootl DirI) -> (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex node idx) -> String
indexPair2Name node idx sidx with (getContentsByDirIndex node idx)
  _ | (_ ** _ ** _ ** (vect, ff)) = shallowIndex2Name vect ff sidx

bool : Bool -> String
bool True = "true"
bool False = "false"

public export
printCOps : Nat -> Nat -> {cfg : NodeCfg} -> (node : Node cfg ar Rootful) -> NodeOps cfg node -> List String
printCOps i len root (GetFlags idx cont) with (indexGet root idx)
    _ | (Evidence _ ((File meta _) ** prf)) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: GetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr;
            int res = ioctl(fd, FAT_IOCTL_GET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            assert(!(attr & ATTR_DIR));
            assert(\#{bool meta.readOnly} == !!(attr & ATTR_RO));
            assert(\#{bool meta.hidden} == !!(attr & ATTR_HIDDEN));
            assert(\#{bool meta.system} == !!(attr & ATTR_SYS));
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
    _ | (Evidence _ ((Dir meta _ _) ** prf)) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: GetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr;
            int res = ioctl(fd, FAT_IOCTL_GET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            assert(attr & ATTR_DIR);
            assert(\#{bool meta.readOnly} == !!(attr & ATTR_RO));
            assert(\#{bool meta.hidden} == !!(attr & ATTR_HIDDEN));
            assert(\#{bool meta.system} == !!(attr & ATTR_SYS));
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
    _ | (Evidence _ ((Root _ _) ** prf)) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: GetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr;
            int res = ioctl(fd, FAT_IOCTL_GET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            assert(attr & ATTR_DIR);
            assert(!(attr & ATTR_RO));
            assert(!(attr & ATTR_HIDDEN));
            assert(!(attr & ATTR_SYS));
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
printCOps i len root (SetFlags idx meta cont) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: SetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr = 0;
            attr |= \#{if meta.readOnly then "ATTR_RO" else "0"};
            attr |= \#{if meta.hidden then "ATTR_HIDDEN" else "0"};
            attr |= \#{if meta.system then "ATTR_SYS" else "0"};
            attr |= \#{if meta.archive then "ATTR_ARCH" else "0"};
            int res = ioctl(fd, FAT_IOCTL_SET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
printCOps i len root (NewDir idx name nameprf cont) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: NewDir \#{name} in \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_PATH | O_DIRECTORY);
            panic_on(fd < 0);
            int res = mkdirat(fd, "\#{name}", 0777);
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
printCOps i len root (NewFile idx name nameprf cont) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: NewFile \#{name} in \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_PATH | O_DIRECTORY);
            panic_on(fd < 0);
            int res = openat(fd, "\#{name}", O_CREAT | O_EXCL | O_WRONLY);
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
printCOps i len root (RmNode idx sidx cont) = let 
  path = index2UnixPath root idx
  name = indexPair2Name root idx sidx
  in #"""
          {
            puts("Test \#{show i}/\#{show len}: RmNode \#{name} in \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_PATH | O_DIRECTORY);
            panic_on(fd < 0);
            int res = fchdir(fd);
            panic_on(res < 0);
            res = rm("\#{name}");
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len _ cont
printCOps _ _ _ Nop = [#"puts("All done!");\#n"#]

public export
buildCProg : (cfg : NodeCfg) -> (root : Node cfg ar Rootful) -> (ops : NodeOps cfg root) -> String
buildCProg cfg root ops = let len = length ops in header len ++ concat (printCOps 1 len root ops) ++ footer
