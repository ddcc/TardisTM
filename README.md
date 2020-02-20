TardisTM
=======

OVERVIEW
--------

TardisTM implements support for transaction repair on top of [TinySTM](https://github.com/patrickmarlier/tinystm). Different variants can be built by modifying the Makefile. For more information, see the [paper](https://www.dcddcc.com/docs/2020_paper_tardistm.pdf).

Information about the repair interface is in the [include/stm.h](https://github.com/ddcc/tardisTM/tree/master/include/stm.h) file, where repair is referred to as merge. To see pre-written abstract operations and repair handlers, refer to our [annotated STAMP repository](https://github.com/ddcc/stamp).

INSTALLATION
------------

Like TinySTM, TardisTM requires the 'atomic\_ops' library, which must be installed separately. To compile, choose a pre-defined variant below, and execute `make -f <variant>`:

* `Makefile.repair`: TardisTM with all repairs enabled.
* `Makefile.restart`: TardisTM without any repair or tracking functionality.
