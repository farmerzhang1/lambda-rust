# awk program that patches the Makefile generated by Coq.

# Patch the uninstall target to work properly, and to also uninstall stale files.
# Also see <https://coq.inria.fr/bugs/show_bug.cgi?id=4907>.
/^uninstall:/ {
	print "uninstall:";
	print "\tif [ -d \"$$(DSTROOT)\"$$(COQLIBINSTALL)/lrust/ ]; then find \"$$(DSTROOT)\"$$(COQLIBINSTALL)/lrust/ -name \"*.vo\" -print -delete; fi";
	getline;
	next
}

# Patch vio2vo to (a) run "make quick" with the same number of jobs, ensuring
# that the .vio files are up-to-date, and (b) only schedule vio2vo for those
# files where the .vo is *older* than the .vio.
/^vio2vo:/ {
	print "vio2vo:";
	print "\t@make -j $(J) quick"
	print "\t@VIOFILES=$$(for file in $(VOFILES:%.vo=%.vio); do vofile=\"$$(echo \"$$file\" | sed \"s/\\.vio/.vo/\")\"; if [ \"$$vofile\" -ot \"$$file\" -o ! -e \"$$vofile\" ]; then echo -n \"$$file \"; fi; done); \\"
	print "\t echo \"VIO2VO: $$VIOFILES\"; \\"
	print "\t if [ -n \"$$VIOFILES\" ]; then $(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $$VIOFILES; fi"
	getline;
	next
}

# This forwards all unchanged lines
1
