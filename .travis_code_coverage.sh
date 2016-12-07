#! /usr/bin/env bash

set -e -u -o pipefail

if [[ "$TRAVIS_OS_NAME" == "osx" ]] ; then
  echo "Skipping coverage on OSX."
  exit
fi

sudo apt-get install libcurl4-openssl-dev libelf-dev libdw-dev

wget https://github.com/simonkagstrom/kcov/archive/master.tar.gz

tar xzf master.tar.gz
mkdir kcov-master/build
cd kcov-master/build

cmake ..
make
sudo make install
cd ../..

kcov --coveralls-id=$travis_job_id --exclude-pattern=/.cargo target/kcov target/debug/duct-*
