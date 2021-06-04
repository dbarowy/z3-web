@if not exist certs mkdir certs
@openssl.exe req -nodes -new -x509 -keyout certs\z3web.key -out certs\z3web.cert
