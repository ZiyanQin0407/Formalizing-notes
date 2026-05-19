#!/bin/bash
set -e

# Update package manager
sudo apt-get update
sudo apt-get install -y curl git wget

# Install elan (Lean version manager)
echo "Installing elan..."
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add Lean to PATH
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc

# Install Lean 4 latest stable version
echo "Installing Lean 4..."
$HOME/.elan/bin/elan default leanprover/lean4:stable

# Verify installation
echo "Verifying Lean installation..."
$HOME/.elan/bin/lean --version

echo "Lean 4 installation completed successfully!"
