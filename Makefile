all: report archive

report:
	pandoc report/report.md -o report.pdf

archive:
	cp -r . /tmp/Lambda-Coq
	rm -rf /tmp/Lambda-Coq/.git
	rm -rf /tmp/Lambda-Coq/.gitignore
	rm -rf /tmp/Lambda-Coq/.lia.cache
	rm -rf /tmp/Lambda-Coq/src/.lia.cache
	tar -czvf ../Lambda-Coq.tar.gz /tmp/Lambda-Coq
	rm -rf /tmp/Lambda-Coq

.PHONY: all report archive
