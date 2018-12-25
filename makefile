PROC=mipsjt
__CFLAGS=-std=c++11
include ../plugin.mak


# MAKEDEP dependency list ------------------
$(F)mipsjt$(O)     :  $(I)bytes.hpp $(I)auto.hpp $(I)loader.hpp       \
	         	$(I)ida.hpp $(I)idp.hpp $(I)kernwin.hpp $(I)name.hpp     \
	          	$(I)offset.hpp $(I)../module/jptcmn.cpp mipsjt.cpp
