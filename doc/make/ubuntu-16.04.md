Installing Lean on Ubuntu 16.04
-------------------------------

### Basic packages

```bash
sudo apt-get install git libgmp-dev cmake ccache
```

### Install step

After building Lean you can install it to the default location (/usr/local/lib/lean)
with the following:

```bash
sudo make install
```