
from pathlib import Path
import os, json

class NEORV32Config:
    def __init__(self, path: None):
        if path is None:
            path = Path(os.path.abspath(__file__)).parent / "latencies.json"
        with open(path) as file:
            self.data = json.loads(file.read())

    @property
    def inst_lat(self):
        return self.data["T_inst_latency"]["measured"]

    @property
    def max_inst_lat(self):
        return self.data["T_inst_latency"]["max"]

    @property
    def min_inst_lat(self):
        return self.data["T_inst_latency"]["min"]

    @property
    def data_lat(self):
        return self.data["T_data_latency"]["measured"]

    @property
    def max_data_lat(self):
        return self.data["T_data_latency"]["max"]

    @property
    def min_data_lat(self):
        return self.data["T_data_latency"]["min"]
    
    @property
    def clock_freq(self):
        return self.dasta["CLOCK_FREQUENCY"]
