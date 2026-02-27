import os

# Enable MPS fallback for ops not yet supported on Apple Silicon.
# Must be set before torch is imported.
os.environ.setdefault("PYTORCH_ENABLE_MPS_FALLBACK", "1")
