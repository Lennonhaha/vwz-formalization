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
# The entry point is inherited from the base image: it already points at the Isabelle
# tool wrapper, and it uses an absolute path (an exec-form `ENTRYPOINT ["isabelle"]`
# fails with "executable file not found in $PATH" because that lookup does not use the
# image's PATH at container start).
FROM makarius/isabelle:Isabelle2025-2

WORKDIR /workspace
COPY . /workspace
