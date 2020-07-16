## Isabelle/Pure on Isabelle2020

FROM ubuntu-latest
SHELL ["/bin/bash", "-c"]

# packages
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get -y update && \
  apt-get install -y curl less libfontconfig1 libgomp1 libwww-perl rlwrap unzip && \
  apt-get clean

# user
RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

# Isabelle
WORKDIR /home/isabelle
ADD --chown=isabelle:isabelle https://isabelle.in.tum.de/dist/Isabelle2020_linux.tar.gz Isabelle.tar.gz
RUN tar xzf Isabelle.tar.gz &&\
  mv Isabelle2020 Isabelle &&\
  perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$USER_HOME/.isabelle",g;' Isabelle/etc/settings &&\
  perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=Pure,g;' Isabelle/etc/settings &&\
  Isabelle/bin/isabelle build -o system_heaps -b Pure &&\
  rm Isabelle.tar.gz

ENTRYPOINT ["Isabelle/bin/isabelle"]

