from __future__ import annotations

from enum import Enum


class BinderStyle(Enum):
    DEFAULT = "default"
    IMPLICIT = "implicit"
    STRICT_IMPLICIT = "strictImplicit"
    INSTANCE_IMPLICIT = "instImplicit"
