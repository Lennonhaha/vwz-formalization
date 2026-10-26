# One-command replication of the VWZ formalization.
#
# The image is deliberately thin. The official Isabelle image already contains the
# distribution, the JDK and the system libraries it needs, so there is nothing to
# download here. Hand-rolling it from a tarball would add ~3 GB to the image and one
# more version string to get wrong (the release is `Isabelle2025-2`, not `Isabelle2025`).
#
#   docker build -t vwz .
#   docker run --rm -v "$PWD:/workspace" -w /workspace vwz build -b -c -D aligned
#
# Two details are deliberate:
#
# * No WORKDIR. The base image's entry point is a *relative* path (`Isabelle/bin/isabelle`),
#   so it resolves against its own working directory. Setting WORKDIR here breaks the
#   inherited entry point ("exec: Isabelle/bin/isabelle: no such file or directory"),
#   and an absolute `ENTRYPOINT ["isabelle"]` does not work either, because that lookup
#   does not use the image's PATH at container start. Keep the working directory the base
#   image chose, and pass `-w /workspace` at run time.
# * No credentials, no build tooling: the container is for reproducing a build, not for
#   developing inside.
FROM makarius/isabelle:Isabelle2025-2

COPY . /workspace
