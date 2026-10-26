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
# The entry point is set explicitly so `build ...` means `isabelle build ...`
# regardless of what the base image does.
FROM makarius/isabelle:Isabelle2025-2

WORKDIR /workspace
COPY . /workspace

ENTRYPOINT ["isabelle"]
