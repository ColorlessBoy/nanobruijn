"""Domain errors exposed by the public checking API."""


class PyNanobruijnError(Exception):
    """Base class for errors caused by an export or a failed kernel check."""


class ParseError(PyNanobruijnError):
    """The NDJSON export is malformed or refers to unavailable data."""


class KernelError(PyNanobruijnError):
    """A declaration violates a kernel checking rule."""


class UnsupportedFeatureError(PyNanobruijnError):
    """The export uses a feature not yet implemented by this port."""
