#!/bin/sh

mkdir -p certs
openssl req -nodes -new -x509 -keyout certs/z3web.key -out certs/z3web.cert
