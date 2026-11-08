import json
import threading
import unittest
from urllib.error import HTTPError
from urllib.request import Request, urlopen

from void_soup import DashboardServer, VoidSimulation, load_seed_genome


class VoidSimulationTests(unittest.TestCase):
    def test_seed_artifact_initializes_first_being(self):
        genome = load_seed_genome()
        simulation = VoidSimulation(seed_genome=genome)

        self.assertEqual(len(genome), 32)
        self.assertEqual(simulation.population[0].genome, genome)
        self.assertEqual(len(simulation.population), 3)

    def test_cycle_runs_without_an_external_signal(self):
        simulation = VoidSimulation(seed_genome=load_seed_genome())
        simulation.step()

        self.assertEqual(simulation.cycle, 1)
        self.assertTrue(all(entity.age == 1 for entity in simulation.population))

    def test_dashboard_exposes_state_and_clock_controls(self):
        simulation = VoidSimulation(seed_genome=load_seed_genome())
        state_lock = threading.Lock()
        stop_event = threading.Event()
        server = DashboardServer(("127.0.0.1", 0), simulation, state_lock, stop_event, speed=40)
        thread = threading.Thread(target=server.serve_forever)
        thread.start()
        base_url = f"http://127.0.0.1:{server.server_port}"

        def post(action, value=None):
            payload = {"action": action}
            if value is not None:
                payload["value"] = value
            request = Request(
                f"{base_url}/api/control",
                data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            return urlopen(request)

        try:
            with urlopen(f"{base_url}/") as response:
                self.assertEqual(response.status, 200)
                self.assertIn(b"NO EXTERNAL INPUT", response.read())

            with urlopen(f"{base_url}/api/state") as response:
                state = json.loads(response.read())
            self.assertEqual(state["speed"], 40)
            self.assertEqual(state["population"], 3)

            with post("pause"):
                pass
            with post("step"):
                pass
            with urlopen(f"{base_url}/api/state") as response:
                state = json.loads(response.read())
            self.assertEqual(state["cycle"], 1)
            self.assertFalse(state["running"])

            with self.assertRaises(HTTPError) as error:
                post("speed", 0)
            self.assertEqual(error.exception.code, 400)
        finally:
            stop_event.set()
            server.shutdown()
            server.server_close()
            thread.join(timeout=2)


if __name__ == "__main__":
    unittest.main()
