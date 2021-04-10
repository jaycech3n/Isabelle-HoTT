## Isabelle2020 Dockerfile for GitHub Actions

FROM ubuntu
SHELL ["/bin/bash", "-c"]

# Install packages
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get -y update &&\
  apt-get install -y curl less libfontconfig1 libgomp1 libwww-perl rlwrap unzip &&\
  apt-get clean

# Set up Isabelle
ADD https://isabelle.in.tum.de/website-Isabelle2020/dist/Isabelle2020_linux.tar.gz Isabelle.tar.gz
RUN tar xzf Isabelle.tar.gz &&\
  mv Isabelle2020 Isabelle &&\
  perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$HOME/.isabelle",g;' Isabelle/etc/settings &&\
  perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=Pure,g;' Isabelle/etc/settings &&\
  Isabelle/bin/isabelle build -o system_heaps -b Pure &&\
  rm Isabelle.tar.gz

# Set up entrypoint
COPY entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]

