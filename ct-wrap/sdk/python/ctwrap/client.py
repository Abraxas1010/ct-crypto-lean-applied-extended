import base64
import json
from dataclasses import dataclass
from typing import List, Optional, Dict, Any

import requests


@dataclass
class WrapResult:
    package: str
    package_hash: str


class CTWrapClient:
    def __init__(self, base_url: str):
        self.base_url = base_url.rstrip("/")

    def wrap(self, data: bytes, recipients: List[str], content_type: Optional[str] = None,
             generate_proof: bool = False, circuit: Optional[str] = None) -> WrapResult:
        payload: Dict[str, Any] = {
            "data": base64.b64encode(data).decode("ascii"),
            "recipients": recipients,
            "content_type": content_type,
            "generate_proof": generate_proof,
            "circuit": circuit,
        }
        r = requests.post(f"{self.base_url}/api/v1/wrap", data=json.dumps(payload),
                          headers={"content-type": "application/json"})
        r.raise_for_status()
        j = r.json()
        return WrapResult(package=j["package"], package_hash=j["package_hash"])
