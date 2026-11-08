import argparse
import json
import math
import random
import threading
import time
from collections import Counter, deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse


GRID_SIZE = 64
RAM_SIZE = 96
GENOME_SIZE = 48

MIN_POPULATION = 8
MAX_POPULATION = 512

VM_STEPS = 12
MAX_PROGRAM_LENGTH = 48
MAX_CONCEPTS = 128
MAX_LEXICON = 192
MAX_MEMORIES = 64
MAX_EVENTS = 100

RESOURCE_REGEN = 0.025
BASE_METABOLIC_COST = 0.35

LANGUAGE_MUTATION_RATE = 0.035
PROGRAM_MUTATION_RATE = 0.045
GENOME_MUTATION_RATE = 0.12


# ---------------------------------------------------------------------------
# Evolved machine language
# ---------------------------------------------------------------------------
#
# Programs are tuples:
#
#     (opcode, a, b)
#
# They execute ONLY inside this VM. They cannot execute Python, access files,
# run shell commands, access the network, or escape the simulation.
#
#  0 NOP
#  1 ADD
#  2 SUB
#  3 MUL
#  4 COPY
#  5 RAND
#  6 MOVE
#  7 HARVEST
#  8 EMIT
#  9 LISTEN
# 10 SENSE
# 11 WRITE
# 12 READ
# 13 LEARN
# 14 TEACH
# 15 REMEMBER
# 16 ABSTRACTION
# 17 EXEC
# 18 IFGT
# 19 IFLT
# 20 REPRO
# 21 SIGNAL
# 22 DIG
# 23 STOP


class SpatialTile:
    def __init__(self, x, y):
        self.x = x
        self.y = y

        self.resource = random.uniform(1.0, 6.0)
        self.toxicity = 0.0

        # Environmental cultural memory.
        self.inscription = deque(maxlen=24)

        # Short-lived communication channel.
        self.signals = deque(maxlen=16)

        self.last_modifier = None

    def tick(self):
        self.resource = min(
            10.0,
            self.resource + RESOURCE_REGEN,
        )

        self.toxicity *= 0.998

        self.signals = deque(
            (
                token,
                strength * 0.94,
                source,
            )
            for token, strength, source in self.signals
            if strength > 0.08
        )

    def add_signal(self, token, strength, source):
        self.signals.append(
            (
                float(token),
                float(strength),
                source,
            )
        )


class Entity:
    """
    A complete digital organism.

    Genetic state:
        genome

    Individual cognitive state:
        RAM
        concepts
        social memory

    Cultural state:
        lexicon
        cultural memory
        learned programs
        program abstractions

    Every field is initialized here so descendants cannot crash because
    some cultural/cognitive attribute doesn't exist.
    """

    def __init__(
        self,
        entity_id,
        x=None,
        y=None,
        genome=None,
        parent=None,
        inherit_culture=True,
    ):
        self.entity_id = entity_id

        self.x = (
            x
            if x is not None
            else random.randrange(GRID_SIZE)
        )

        self.y = (
            y
            if y is not None
            else random.randrange(GRID_SIZE)
        )

        self.age = 0
        self.energy = 100.0

        self.generation = (
            0
            if parent is None
            else parent.generation + 1
        )

        # ------------------------------------------------------------------
        # Machine state
        # ------------------------------------------------------------------

        self.ram = [0.0] * RAM_SIZE
        self.ip = 0
        self.vm_steps = 0

        self.genome = (
            [
                random.uniform(-10.0, 10.0)
                for _ in range(GENOME_SIZE)
            ]
            if genome is None
            else list(genome)
        )

        # ------------------------------------------------------------------
        # Cognitive state
        # ------------------------------------------------------------------

        # concept_id ->
        # {
        #     "name": str,
        #     "value": float,
        #     "seen": int
        # }
        self.concepts = {}

        self.concept_counter = 0

        # word -> concept_id
        self.lexicon = {}

        # concept_id -> word
        self.inverse_lexicon = {}

        # ------------------------------------------------------------------
        # Cultural / programming state
        # ------------------------------------------------------------------

        # program name -> list[(opcode, a, b)]
        self.learned_programs = {}

        # program name ->
        # {
        #     "origin": ...,
        #     "uses": int,
        #     "fitness": float
        # }
        self.program_abstractions = {}

        self.cultural_memory = deque(
            maxlen=MAX_MEMORIES
        )

        self.social_memory = {}
        self.tile_memory = {}

        # ------------------------------------------------------------------
        # Statistics
        # ------------------------------------------------------------------

        self.language_stats = {
            "messages_sent": 0,
            "messages_received": 0,
            "successful_interpretations": 0,
            "failed_interpretations": 0,
            "new_words": 0,
            "teach_events": 0,
        }

        self.program_stats = {
            "executions": 0,
            "useful_executions": 0,
            "discoveries": 0,
        }

        # ------------------------------------------------------------------
        # Ephemeral state
        # ------------------------------------------------------------------

        self.last_emitted_token = 0.0
        self.last_meaning = None
        self.last_message = None

        # ------------------------------------------------------------------
        # Cultural inheritance
        # ------------------------------------------------------------------

        if parent is not None and inherit_culture:
            self.inherit_culture_from(parent)

        # These are perceptual categories, not words.
        self.ensure_core_concepts()

    # -----------------------------------------------------------------------
    # Concepts
    # -----------------------------------------------------------------------

    def ensure_core_concepts(self):
        for name in (
            "self",
            "other",
            "food",
            "danger",
            "place",
            "resource",
            "signal",
            "birth",
            "death",
            "program",
            "tool",
            "help",
            "move",
        ):
            self.ensure_concept(name)

    def ensure_concept(self, name):
        for cid, data in self.concepts.items():
            if data["name"] == name:
                return cid

        if len(self.concepts) >= MAX_CONCEPTS:
            weakest = min(
                self.concepts,
                key=lambda cid: self.concepts[cid]["seen"],
            )

            old_word = self.inverse_lexicon.pop(
                weakest,
                None,
            )

            if old_word is not None:
                self.lexicon.pop(
                    old_word,
                    None,
                )

            self.concepts.pop(
                weakest,
                None,
            )

        cid = (
            f"{self.entity_id}:c"
            f"{self.concept_counter}"
        )

        self.concept_counter += 1

        self.concepts[cid] = {
            "name": name,
            "value": 0.0,
            "seen": 1,
        }

        return cid

    # -----------------------------------------------------------------------
    # Cultural inheritance
    # -----------------------------------------------------------------------

    def inherit_culture_from(self, parent):
        """
        Culture is transmitted vertically at reproduction.

        Concept IDs are NOT copied directly because each organism owns its
        own concept namespace.
        """

        parent_concepts = list(
            parent.concepts.items()
        )[:MAX_CONCEPTS]

        for _, data in parent_concepts:
            new_cid = self.ensure_concept(
                data["name"]
            )

            self.concepts[new_cid]["value"] = (
                data["value"]
            )

            self.concepts[new_cid]["seen"] = max(
                1,
                data["seen"] // 2,
            )

        translated_lexicon = {}

        for word, parent_cid in parent.lexicon.items():
            parent_data = parent.concepts.get(
                parent_cid
            )

            if parent_data is None:
                continue

            local_cid = self.ensure_concept(
                parent_data["name"]
            )

            translated_lexicon[word] = local_cid

        self.lexicon = dict(
            list(
                translated_lexicon.items()
            )[:MAX_LEXICON]
        )

        self.inverse_lexicon = {
            cid: word
            for word, cid in self.lexicon.items()
        }

        self.learned_programs = {
            name: [
                tuple(instruction)
                for instruction in program[
                    :MAX_PROGRAM_LENGTH
                ]
            ]
            for name, program in list(
                parent.learned_programs.items()
            )[:24]
        }

        self.program_abstractions = {
            name: dict(metadata)
            for name, metadata in list(
                parent.program_abstractions.items()
            )[:24]
        }

        self.cultural_memory.extend(
            list(
                parent.cultural_memory
            )[-24:]
        )

    # -----------------------------------------------------------------------
    # Genetic mutation
    # -----------------------------------------------------------------------

    def mutate_genome(self):
        for index in range(
            len(self.genome)
        ):
            if random.random() < GENOME_MUTATION_RATE:
                self.genome[index] += random.gauss(
                    0.0,
                    1.15,
                )

                self.genome[index] = max(
                    -20.0,
                    min(
                        20.0,
                        self.genome[index],
                    ),
                )

    # -----------------------------------------------------------------------
    # Cultural mutation
    # -----------------------------------------------------------------------

    def mutate_culture(self):
        # Words mutate independently of concepts.
        for word, concept_id in list(
            self.lexicon.items()
        ):
            if random.random() < LANGUAGE_MUTATION_RATE:
                new_word = mutate_word(word)

                if (
                    new_word != word
                    and new_word not in self.lexicon
                ):
                    self.lexicon.pop(
                        word,
                        None,
                    )

                    self.lexicon[new_word] = (
                        concept_id
                    )

                    self.inverse_lexicon[
                        concept_id
                    ] = new_word

        # Programs mutate while remaining inside the safe VM.
        for name in list(
            self.learned_programs
        ):
            if random.random() < PROGRAM_MUTATION_RATE:
                self.learned_programs[name] = (
                    mutate_program(
                        self.learned_programs[name]
                    )
                )

        # Occasionally turn an existing program into
        # a named cultural abstraction.
        if random.random() < 0.01:
            self.discover_program_abstraction()

    def discover_program_abstraction(self):
        if not self.learned_programs:
            return

        source_name = random.choice(
            list(self.learned_programs)
        )

        source = self.learned_programs[
            source_name
        ]

        if not source:
            return

        name = random_word(
            2,
            4,
        )

        if name in self.learned_programs:
            return

        self.learned_programs[name] = [
            tuple(instruction)
            for instruction in source[:8]
        ]

        self.program_abstractions[name] = {
            "origin": source_name,
            "uses": 0,
            "fitness": 0.0,
        }

        self.program_stats[
            "discoveries"
        ] += 1

    # -----------------------------------------------------------------------
    # Memory
    # -----------------------------------------------------------------------

    def remember(self, item):
        self.cultural_memory.append(item)

    # -----------------------------------------------------------------------
    # Language
    # -----------------------------------------------------------------------

    def word_for(self, concept_id):
        return self.inverse_lexicon.get(
            concept_id
        )

    def concept_for_word(self, word):
        return self.lexicon.get(
            word
        )

    def learn_word(
        self,
        word,
        concept_id,
    ):
        if (
            not word
            or concept_id not in self.concepts
        ):
            return False

        existing = self.lexicon.get(
            word
        )

        if existing == concept_id:
            return True

        if existing is not None:
            self.inverse_lexicon.pop(
                existing,
                None,
            )

        old_word = self.inverse_lexicon.get(
            concept_id
        )

        if old_word:
            self.lexicon.pop(
                old_word,
                None,
            )

        if len(self.lexicon) >= MAX_LEXICON:
            weakest_word = random.choice(
                list(self.lexicon)
            )

            weakest_cid = self.lexicon.pop(
                weakest_word
            )

            self.inverse_lexicon.pop(
                weakest_cid,
                None,
            )

        self.lexicon[word] = concept_id
        self.inverse_lexicon[
            concept_id
        ] = word

        self.language_stats[
            "new_words"
        ] += 1

        return True


# ---------------------------------------------------------------------------
# Language utilities
# ---------------------------------------------------------------------------


def random_word(
    min_syllables=2,
    max_syllables=4,
):
    consonants = (
        "bcdfghjklmnpqrstvwxyz"
    )

    vowels = "aeiou"

    syllables = random.randint(
        min_syllables,
        max_syllables,
    )

    word = ""

    for _ in range(syllables):
        word += (
            random.choice(consonants)
            + random.choice(vowels)
        )

        if random.random() < 0.25:
            word += random.choice(
                consonants
            )

    return word[:10]


def mutate_word(word):
    if not word:
        return random_word()

    chars = list(word)

    operation = random.randrange(4)

    if (
        operation == 0
        and len(chars) > 2
    ):
        chars[
            random.randrange(len(chars))
        ] = random.choice(
            "aeiou"
        )

    elif operation == 1:
        chars.insert(
            random.randrange(
                len(chars) + 1
            ),
            random.choice("aeiou"),
        )

    elif (
        operation == 2
        and len(chars) > 3
    ):
        chars.pop(
            random.randrange(
                len(chars)
            )
        )

    else:
        chars.append(
            random.choice(
                "bcdfghjklmnpqrstvwxyz"
            )
        )

    return "".join(chars)[:10]


# ---------------------------------------------------------------------------
# Program utilities
# ---------------------------------------------------------------------------


def random_instruction():
    return (
        random.randrange(24),
        random.randrange(RAM_SIZE),
        random.randrange(RAM_SIZE),
    )


def mutate_program(program):
    program = [
        tuple(instruction)
        for instruction in program
    ]

    if not program:
        return [
            random_instruction()
        ]

    if (
        random.random() < 0.35
        and len(program) < MAX_PROGRAM_LENGTH
    ):
        program.insert(
            random.randrange(
                len(program) + 1
            ),
            random_instruction(),
        )

    elif (
        random.random() < 0.25
        and len(program) > 2
    ):
        program.pop(
            random.randrange(
                len(program)
            )
        )

    index = random.randrange(
        len(program)
    )

    opcode, a, b = program[index]

    if random.random() < 0.5:
        opcode = random.randrange(24)

    if random.random() < 0.7:
        a = random.randrange(
            RAM_SIZE
        )

    if random.random() < 0.7:
        b = random.randrange(
            RAM_SIZE
        )

    program[index] = (
        opcode,
        a,
        b,
    )

    return program[
        :MAX_PROGRAM_LENGTH
    ]


# ---------------------------------------------------------------------------
# Simulation
# ---------------------------------------------------------------------------


class SpatialVoidSimulation:
    def __init__(
        self,
        initial_population=MIN_POPULATION,
    ):
        self.cycle = 0
        self.entity_counter = 1

        self.population = []

        self.events = deque(
            maxlen=MAX_EVENTS
        )

        self.language_global = Counter()
        self.program_global = Counter()

        self.grid = [
            [
                SpatialTile(
                    x,
                    y,
                )
                for y in range(GRID_SIZE)
            ]
            for x in range(GRID_SIZE)
        ]

        initial_population = max(
            MIN_POPULATION,
            min(
                MAX_POPULATION,
                initial_population,
            ),
        )

        for _ in range(
            initial_population
        ):
            self.spawn_founder()

        self.events.append(
            {
                "cycle": 0,
                "message": (
                    f"World initialized with "
                    f"{len(self.population)} "
                    "autonomous beings."
                ),
            }
        )

    # -----------------------------------------------------------------------
    # Population
    # -----------------------------------------------------------------------

    def spawn_founder(self):
        entity = Entity(
            entity_id=(
                f"Spawn_{self.entity_counter}"
            )
        )

        self.entity_counter += 1

        self.population.append(
            entity
        )

    # -----------------------------------------------------------------------
    # World helpers
    # -----------------------------------------------------------------------

    def add_event(self, message):
        self.events.append(
            {
                "cycle": self.cycle,
                "message": message,
            }
        )

    def tile(self, entity):
        return self.grid[
            entity.x
        ][
            entity.y
        ]

    def nearby_entities(
        self,
        entity,
        radius=2,
    ):
        result = []

        for other in self.population:
            if other is entity:
                continue

            dx = min(
                abs(
                    entity.x
                    - other.x
                ),
                GRID_SIZE
                - abs(
                    entity.x
                    - other.x
                ),
            )

            dy = min(
                abs(
                    entity.y
                    - other.y
                ),
                GRID_SIZE
                - abs(
                    entity.y
                    - other.y
                ),
            )

            if (
                dx <= radius
                and dy <= radius
            ):
                result.append(
                    other
                )

        return result

    # -----------------------------------------------------------------------
    # Perception
    # -----------------------------------------------------------------------

    def create_perceptual_concepts(
        self,
        entity,
    ):
        tile = self.tile(
            entity
        )

        if tile.resource > 5.0:
            cid = entity.ensure_concept(
                "resource-rich"
            )

            entity.concepts[cid][
                "value"
            ] += 0.3

            entity.concepts[cid][
                "seen"
            ] += 1

        if tile.toxicity > 1.0:
            cid = entity.ensure_concept(
                "dangerous-place"
            )

            entity.concepts[cid][
                "value"
            ] += tile.toxicity

            entity.concepts[cid][
                "seen"
            ] += 1

        if tile.signals:
            cid = entity.ensure_concept(
                "signal"
            )

            entity.concepts[cid][
                "value"
            ] += 0.2

            entity.concepts[cid][
                "seen"
            ] += 1

        if self.nearby_entities(
            entity,
            radius=1,
        ):
            cid = entity.ensure_concept(
                "other"
            )

            entity.concepts[cid][
                "seen"
            ] += 1

    # -----------------------------------------------------------------------
    # Language emergence
    # -----------------------------------------------------------------------

    def evolve_language(
        self,
        entity,
    ):
        """
        A concept becomes communicable after repeated experience.

        The organism invents the first word.

        Other organisms can subsequently learn that convention.
        """

        for cid, data in list(
            entity.concepts.items()
        ):
            if data["seen"] < 3:
                continue

            if (
                cid not in entity.inverse_lexicon
                and random.random() < 0.04
            ):
                word = random_word()

                while word in entity.lexicon:
                    word = random_word()

                entity.learn_word(
                    word,
                    cid,
                )

                entity.remember(
                    {
                        "kind": "word-invention",
                        "word": word,
                        "concept": data[
                            "name"
                        ],
                        "cycle": self.cycle,
                    }
                )

                self.add_event(
                    f"{entity.entity_id} invented "
                    f"'{word}' for "
                    f"{data['name']}."
                )

    def choose_message(
        self,
        sender,
    ):
        candidates = []

        for cid, data in (
            sender.concepts.items()
        ):
            word = sender.word_for(
                cid
            )

            if word:
                score = (
                    data["seen"]
                    + abs(
                        data["value"]
                    ) * 0.1
                )

                candidates.append(
                    (
                        score,
                        cid,
                        word,
                    )
                )

        if not candidates:
            return None

        candidates.sort(
            reverse=True
        )

        _, cid, word = candidates[0]

        intensity = max(
            -1.0,
            min(
                1.0,
                sender.concepts[cid][
                    "value"
                ] / 10.0,
            ),
        )

        return {
            "word": word,
            "signal": intensity,
            "concept_hint": sender.concepts[
                cid
            ]["name"],
            "sender_concept": cid,
        }

    def communicate(
        self,
        sender,
        receiver,
    ):
        message = self.choose_message(
            sender
        )

        if message is None:
            return

        sender.language_stats[
            "messages_sent"
        ] += 1

        receiver.language_stats[
            "messages_received"
        ] += 1

        word = message["word"]

        learned_cid = (
            receiver.concept_for_word(
                word
            )
        )

        # Known word.
        if learned_cid is not None:
            receiver.language_stats[
                "successful_interpretations"
            ] += 1

            receiver.social_memory[
                sender.entity_id
            ] = {
                "word": word,
                "concept": receiver.concepts[
                    learned_cid
                ]["name"],
                "cycle": self.cycle,
            }

            receiver.remember(
                {
                    "kind": "understood",
                    "from": sender.entity_id,
                    "word": word,
                    "concept": receiver.concepts[
                        learned_cid
                    ]["name"],
                    "cycle": self.cycle,
                }
            )

            return

        # Unknown word.
        receiver.language_stats[
            "failed_interpretations"
        ] += 1

        possible = list(
            receiver.concepts
        )

        if not possible:
            return

        inferred = max(
            possible,
            key=lambda cid: (
                self.concept_similarity(
                    receiver.concepts[cid][
                        "name"
                    ],
                    message[
                        "concept_hint"
                    ],
                )
            ),
        )

        # The receiver occasionally adopts its interpretation.
        if random.random() < 0.38:
            receiver.learn_word(
                word,
                inferred,
            )

            receiver.language_stats[
                "teach_events"
            ] += 1

            receiver.remember(
                {
                    "kind": "language-learning",
                    "from": sender.entity_id,
                    "word": word,
                    "concept": receiver.concepts[
                        inferred
                    ]["name"],
                    "cycle": self.cycle,
                }
            )

    @staticmethod
    def concept_similarity(
        a,
        b,
    ):
        """
        Very weak structural bias.

        There is no English dictionary or language model here.
        """

        if a == b:
            return 1.0

        prefix = 0

        for left, right in zip(
            a,
            b,
        ):
            if left != right:
                break

            prefix += 1

        return prefix / max(
            len(a),
            len(b),
            1,
        )

    # -----------------------------------------------------------------------
    # Cultural exchange
    # -----------------------------------------------------------------------

    def exchange_culture(
        self,
        entity,
    ):
        neighbors = self.nearby_entities(
            entity,
            radius=1,
        )

        if not neighbors:
            return

        partner = random.choice(
            neighbors
        )

        self.communicate(
            entity,
            partner,
        )

        if random.random() < 0.7:
            self.communicate(
                partner,
                entity,
            )

        # Executable culture spreads much more slowly than words.
        if (
            partner.learned_programs
            and random.random() < 0.08
        ):
            name = random.choice(
                list(
                    partner.learned_programs
                )
            )

            program = partner.learned_programs[
                name
            ]

            if name not in entity.learned_programs:
                entity.learned_programs[
                    name
                ] = [
                    tuple(instruction)
                    for instruction in program
                ]

                entity.program_abstractions[
                    name
                ] = {
                    "origin": partner.entity_id,
                    "uses": 0,
                    "fitness": 0.0,
                }

                self.add_event(
                    f"{entity.entity_id} learned "
                    f"program '{name}' from "
                    f"{partner.entity_id}."
                )

    # -----------------------------------------------------------------------
    # VM
    # -----------------------------------------------------------------------

    def execute_opcode(
        self,
        entity,
        opcode,
        a,
        b,
    ):
        a %= RAM_SIZE
        b %= RAM_SIZE

        tile = self.tile(
            entity
        )

        # ---------------------------------------------------------------
        # Arithmetic
        # ---------------------------------------------------------------

        if opcode == 0:
            return False

        if opcode == 1:
            entity.ram[a] += (
                entity.ram[b]
            )

        elif opcode == 2:
            entity.ram[a] -= (
                entity.ram[b]
            )

        elif opcode == 3:
            entity.ram[a] *= (
                entity.ram[b]
            )

            # Prevent runaway floating-point values.
            entity.ram[a] = max(
                -1e6,
                min(
                    1e6,
                    entity.ram[a],
                ),
            )

        elif opcode == 4:
            entity.ram[a] = (
                entity.ram[b]
            )

        elif opcode == 5:
            # Deterministic pseudo-randomness.
            # This avoids giving the VM direct access to Python's random
            # internals while still allowing stochastic programs.
            seed = (
                self.cycle * 131
                + entity.age * 17
                + entity.ip * 7
                + a * 3
                + stable_entity_hash(
                    entity.entity_id
                )
            )

            entity.ram[a] = (
                math.sin(
                    seed * 0.017
                )
                * 0.5
                + 0.5
            )

        # ---------------------------------------------------------------
        # Movement
        # ---------------------------------------------------------------

        elif opcode == 6:
            direction = int(
                abs(
                    entity.ram[a]
                    + entity.ram[b]
                )
            ) % 4

            if direction == 0:
                entity.y = (
                    entity.y - 1
                ) % GRID_SIZE

            elif direction == 1:
                entity.y = (
                    entity.y + 1
                ) % GRID_SIZE

            elif direction == 2:
                entity.x = (
                    entity.x + 1
                ) % GRID_SIZE

            else:
                entity.x = (
                    entity.x - 1
                ) % GRID_SIZE

            entity.energy -= 0.12

        # ---------------------------------------------------------------
        # Environment
        # ---------------------------------------------------------------

        elif opcode == 7:
            harvested = min(
                tile.resource,
                1.5,
            )

            tile.resource -= harvested
            entity.energy += harvested

        elif opcode == 8:
            concept_ids = [
                cid
                for cid in entity.concepts
                if entity.word_for(cid)
            ]

            if concept_ids:
                cid = max(
                    concept_ids,
                    key=lambda item:
                    entity.concepts[item][
                        "seen"
                    ],
                )

                word = entity.word_for(
                    cid
                )

                entity.last_emitted_token = (
                    stable_token(word)
                )

                entity.last_message = word

                tile.add_signal(
                    entity.last_emitted_token,
                    1.0,
                    entity.entity_id,
                )

        elif opcode == 9:
            if tile.signals:
                token, strength, _source = max(
                    tile.signals,
                    key=lambda item:
                    item[1],
                )

                entity.ram[a] = (
                    token * strength
                )

        elif opcode == 10:
            entity.ram[a] = (
                tile.resource
                - tile.toxicity
                + len(tile.signals)
                * 0.2
            )

        elif opcode == 11:
            value = entity.ram[a]

            tile.inscription.append(
                float(value)
            )

            tile.last_modifier = (
                entity.entity_id
            )

            if len(tile.inscription) >= 3:
                self.try_compile_tile(
                    entity,
                    tile,
                )

        elif opcode == 12:
            entity.ram[a] = (
                tile.inscription[-1]
                if tile.inscription
                else 0.0
            )

        # ---------------------------------------------------------------
        # Language / culture
        # ---------------------------------------------------------------

        elif opcode == 13:
            self.learn_from_environment(
                entity,
                a,
                b,
            )

        elif opcode == 14:
            self.teach_neighbor(
                entity
            )

        elif opcode == 15:
            entity.remember(
                {
                    "kind": "association",
                    "value": round(
                        entity.ram[a],
                        4,
                    ),
                    "cycle": self.cycle,
                }
            )

        # ---------------------------------------------------------------
        # Programming
        # ---------------------------------------------------------------

        elif opcode == 16:
            self.learn_program_from_ram(
                entity
            )

        elif opcode == 17:
            self.execute_learned_abstraction(
                entity
            )

        # ---------------------------------------------------------------
        # Control flow
        # ---------------------------------------------------------------

        elif opcode == 18:
            if entity.ram[a] <= entity.ram[b]:
                entity.ip = (
                    entity.ip + 1
                ) % GENOME_SIZE

        elif opcode == 19:
            if entity.ram[a] >= entity.ram[b]:
                entity.ip = (
                    entity.ip + 1
                ) % GENOME_SIZE

        # ---------------------------------------------------------------
        # Reproduction
        # ---------------------------------------------------------------

        elif opcode == 20:
            if entity.energy > 145.0:
                return "reproduce"

        # ---------------------------------------------------------------
        # Persistent signal
        # ---------------------------------------------------------------

        elif opcode == 21:
            tile.add_signal(
                entity.ram[a],
                1.5,
                entity.entity_id,
            )

        # ---------------------------------------------------------------
        # Environmental programming
        # ---------------------------------------------------------------

        elif opcode == 22:
            amount = max(
                0.0,
                min(
                    1.0,
                    abs(
                        entity.ram[a]
                    ) * 0.05,
                ),
            )

            tile.resource = min(
                10.0,
                tile.resource + amount,
            )

            tile.toxicity = max(
                0.0,
                tile.toxicity
                - amount * 0.1,
            )

        elif opcode == 23:
            return "stop"

        return False

    # -----------------------------------------------------------------------
    # Learning
    # -----------------------------------------------------------------------

    def learn_from_environment(
        self,
        entity,
        a,
        b,
    ):
        tile = self.tile(
            entity
        )

        if tile.resource > 4.0:
            cid = entity.ensure_concept(
                "resource-rich"
            )

        elif tile.toxicity > 1.0:
            cid = entity.ensure_concept(
                "dangerous-place"
            )

        else:
            cid = entity.ensure_concept(
                "place"
            )

        entity.concepts[cid][
            "seen"
        ] += 1

        entity.concepts[cid][
            "value"
        ] += entity.ram[a] * 0.01

        word = entity.word_for(
            cid
        )

        if (
            word is None
            and random.random() < 0.3
        ):
            entity.learn_word(
                random_word(),
                cid,
            )

    def teach_neighbor(
        self,
        entity,
    ):
        neighbors = self.nearby_entities(
            entity,
            radius=1,
        )

        if not neighbors:
            return

        target = random.choice(
            neighbors
        )

        message = self.choose_message(
            entity
        )

        if not message:
            return

        target.language_stats[
            "messages_received"
        ] += 1

        sender_cid = message[
            "sender_concept"
        ]

        sender_data = entity.concepts.get(
            sender_cid
        )

        if sender_data is None:
            return

        target_cid = target.ensure_concept(
            sender_data["name"]
        )

        if target.learn_word(
            message["word"],
            target_cid,
        ):
            target.language_stats[
                "teach_events"
            ] += 1

    # -----------------------------------------------------------------------
    # Program construction
    # -----------------------------------------------------------------------

    def learn_program_from_ram(
        self,
        entity,
    ):
        """
        A being can construct a program from its own memory.

        The resulting program is still constrained to the 24 safe VM
        instructions.
        """

        length = (
            2
            + int(
                abs(
                    entity.ram[0]
                )
            ) % 8
        )

        program = []

        for i in range(length):
            base = (
                i * 3
            ) % RAM_SIZE

            opcode = (
                int(
                    abs(
                        entity.ram[base]
                    )
                ) % 24
            )

            a = (
                int(
                    abs(
                        entity.ram[
                            (base + 1)
                            % RAM_SIZE
                        ]
                    )
                )
                % RAM_SIZE
            )

            b = (
                int(
                    abs(
                        entity.ram[
                            (base + 2)
                            % RAM_SIZE
                        ]
                    )
                )
                % RAM_SIZE
            )

            program.append(
                (
                    opcode,
                    a,
                    b,
                )
            )

        name = random_word(
            2,
            3,
        )

        entity.learned_programs[
            name
        ] = program

        entity.program_abstractions[
            name
        ] = {
            "origin": entity.entity_id,
            "uses": 0,
            "fitness": 0.0,
        }

    def execute_learned_abstraction(
        self,
        entity,
    ):
        if not entity.learned_programs:
            return

        name = max(
            entity.learned_programs,
            key=lambda n:
            entity.program_abstractions.get(
                n,
                {},
            ).get(
                "fitness",
                0.0,
            ),
        )

        program = entity.learned_programs[
            name
        ]

        before = entity.energy

        entity.program_stats[
            "executions"
        ] += 1

        for (
            opcode,
            a,
            b,
        ) in program[:8]:
            result = self.execute_opcode(
                entity,
                opcode,
                a,
                b,
            )

            if result in (
                "stop",
                "reproduce",
            ):
                break

        delta = (
            entity.energy
            - before
        )

        metadata = (
            entity.program_abstractions
            .setdefault(
                name,
                {
                    "origin":
                    entity.entity_id,
                    "uses": 0,
                    "fitness": 0.0,
                },
            )
        )

        metadata["uses"] += 1

        metadata["fitness"] = (
            metadata["fitness"]
            * 0.95
            + delta
            * 0.05
        )

        if delta > 0.2:
            entity.program_stats[
                "useful_executions"
            ] += 1

    # -----------------------------------------------------------------------
    # Environmental programming
    # -----------------------------------------------------------------------

    def try_compile_tile(
        self,
        entity,
        tile,
    ):
        """
        The environment itself becomes a second cultural substrate.

        A simple numerical pattern can be discovered and turned into a
        reusable executable abstraction.
        """

        values = list(
            tile.inscription
        )[-3:]

        a, b, c = values

        # Addition pattern.
        if abs(
            (a + b) - c
        ) < 0.25:
            tile.resource = min(
                10.0,
                tile.resource + 3.0,
            )

            entity.energy += 1.5

            tile.inscription.clear()

            name = random_word(
                2,
                3,
            )

            entity.learned_programs.setdefault(
                name,
                [
                    (7, 0, 1),
                    (22, 1, 2),
                ],
            )

            entity.program_abstractions.setdefault(
                name,
                {
                    "origin":
                    (
                        f"tile:"
                        f"{tile.x}:"
                        f"{tile.y}"
                    ),
                    "uses": 0,
                    "fitness": 0.5,
                },
            )

            self.add_event(
                f"{entity.entity_id} discovered "
                f"environmental program "
                f"'{name}' at "
                f"({tile.x},{tile.y})."
            )

        # Dangerous multiplication pattern.
        elif abs(
            a * b
        ) > 50.0:
            tile.toxicity = min(
                20.0,
                tile.toxicity + 1.0,
            )

            tile.inscription.clear()

    # -----------------------------------------------------------------------
    # Organism lifecycle
    # -----------------------------------------------------------------------

    def run_vm_cycle(
        self,
        entity,
    ):
        self.create_perceptual_concepts(
            entity
        )

        self.evolve_language(
            entity
        )

        reproduction_requested = False

        for _ in range(
            VM_STEPS
        ):
            opcode = (
                int(
                    abs(
                        entity.genome[
                            entity.ip
                        ]
                    )
                ) % 24
            )

            arg1 = (
                int(
                    abs(
                        entity.genome[
                            (
                                entity.ip
                                + 1
                            )
                            % GENOME_SIZE
                        ]
                    )
                )
                % RAM_SIZE
            )

            arg2 = (
                int(
                    abs(
                        entity.genome[
                            (
                                entity.ip
                                + 2
                            )
                            % GENOME_SIZE
                        ]
                    )
                )
                % RAM_SIZE
            )

            result = self.execute_opcode(
                entity,
                opcode,
                arg1,
                arg2,
            )

            entity.vm_steps += 1

            if result == "reproduce":
                reproduction_requested = True
                break

            if result == "stop":
                break

            entity.ip = (
                entity.ip + 1
            ) % GENOME_SIZE

        tile = self.tile(
            entity
        )

        if tile.toxicity > 0:
            entity.energy -= (
                tile.toxicity
                * 0.08
            )

        entity.energy -= (
            BASE_METABOLIC_COST
        )

        entity.age += 1

        # Culture happens through interaction.
        self.exchange_culture(
            entity
        )

        entity.mutate_culture()

        return reproduction_requested

    # -----------------------------------------------------------------------
    # Reproduction
    # -----------------------------------------------------------------------

    def reproduce(
        self,
        parent,
    ):
        if (
            len(self.population)
            >= MAX_POPULATION
        ):
            return None

        child_x = (
            parent.x
            + random.choice(
                [-1, 0, 1]
            )
        ) % GRID_SIZE

        child_y = (
            parent.y
            + random.choice(
                [-1, 0, 1]
            )
        ) % GRID_SIZE

        child = Entity(
            entity_id=(
                f"Gen_"
                f"{self.entity_counter}"
            ),
            x=child_x,
            y=child_y,
            genome=parent.genome,
            parent=parent,
            inherit_culture=True,
        )

        self.entity_counter += 1

        # Biological variation.
        child.mutate_genome()

        # Cultural variation.
        child.mutate_culture()

        # Physical cost of reproduction.
        parent.energy -= 55.0

        child.energy = 72.0

        self.add_event(
            f"{child.entity_id} born from "
            f"{parent.entity_id}; "
            f"generation "
            f"{child.generation}."
        )

        return child

    # -----------------------------------------------------------------------
    # Simulation step
    # -----------------------------------------------------------------------

    def step(self):
        self.cycle += 1

        for row in self.grid:
            for tile in row:
                tile.tick()

        births = []
        survivors = []

        # Snapshot is important:
        # newborns do not get an extra simulation turn this cycle.
        for entity in list(
            self.population
        ):
            try:
                reproduction_requested = (
                    self.run_vm_cycle(
                        entity
                    )
                )

                if (
                    reproduction_requested
                    and entity.energy >= 145.0
                ):
                    child = self.reproduce(
                        entity
                    )

                    if child is not None:
                        births.append(
                            child
                        )

                if entity.energy > 0.0:
                    survivors.append(
                        entity
                    )
                else:
                    self.add_event(
                        f"{entity.entity_id} "
                        f"died at "
                        f"({entity.x},"
                        f"{entity.y})."
                    )

            except Exception as error:
                # An invalid organism cannot crash the entire world.
                self.add_event(
                    f"{entity.entity_id} "
                    f"was removed after "
                    f"internal error: "
                    f"{type(error).__name__}: "
                    f"{error}"
                )

        survivors.extend(
            births
        )

        self.population = survivors[
            :MAX_POPULATION
        ]

        # Population floor.
        while len(
            self.population
        ) < MIN_POPULATION:
            self.spawn_founder()

        # Rebuild global cultural statistics.
        self.language_global.clear()
        self.program_global.clear()

        for entity in self.population:
            for word in entity.lexicon:
                self.language_global[
                    word
                ] += 1

            for program in entity.learned_programs:
                self.program_global[
                    program
                ] += 1

    # -----------------------------------------------------------------------
    # Dashboard snapshot
    # -----------------------------------------------------------------------

    def snapshot(
        self,
        running,
        speed,
    ):
        energies = [
            entity.energy
            for entity in self.population
        ]

        top_languages = (
            self.language_global
            .most_common(12)
        )

        top_programs = (
            self.program_global
            .most_common(12)
        )

        entities = []

        for entity in sorted(
            self.population,
            key=lambda item:
            item.energy,
            reverse=True,
        )[:40]:
            entities.append(
                {
                    "id":
                        entity.entity_id,
                    "generation":
                        entity.generation,
                    "age":
                        entity.age,
                    "energy":
                        round(
                            entity.energy,
                            2,
                        ),
                    "x":
                        entity.x,
                    "y":
                        entity.y,
                    "words":
                        len(
                            entity.lexicon
                        ),
                    "concepts":
                        len(
                            entity.concepts
                        ),
                    "programs":
                        len(
                            entity.learned_programs
                        ),
                    "messages":
                        (
                            entity.language_stats[
                                "messages_sent"
                            ]
                            + entity.language_stats[
                                "messages_received"
                            ]
                        ),
                    "useful_programs":
                        entity.program_stats[
                            "useful_executions"
                        ],
                }
            )

        return {
            "cycle":
                self.cycle,

            "population":
                len(
                    self.population
                ),

            "average_energy":
                (
                    sum(energies)
                    / len(energies)
                    if energies
                    else 0.0
                ),

            "running":
                running,

            "speed":
                speed,

            "grid_size":
                GRID_SIZE,

            "language_vocabulary":
                len(
                    self.language_global
                ),

            "program_culture":
                len(
                    self.program_global
                ),

            "dominant_words":
                [
                    {
                        "word":
                            word,
                        "population":
                            count,
                    }
                    for word, count
                    in top_languages
                ],

            "dominant_programs":
                [
                    {
                        "program":
                            name,
                        "population":
                            count,
                    }
                    for name, count
                    in top_programs
                ],

            "entities":
                entities,

            "events":
                list(
                    reversed(
                        self.events
                    )
                ),
        }


# ---------------------------------------------------------------------------
# Deterministic hashes
# ---------------------------------------------------------------------------


def stable_entity_hash(
    value,
):
    result = 2166136261

    for char in value:
        result ^= ord(char)
        result = (
            result * 16777619
        ) & 0xFFFFFFFF

    return result


def stable_token(
    word,
):
    return (
        stable_entity_hash(word)
        / 0xFFFFFFFF
    )


# ---------------------------------------------------------------------------
# HTTP dashboard
# ---------------------------------------------------------------------------


class DashboardServer(
    ThreadingHTTPServer
):
    daemon_threads = True
    allow_reuse_address = True

    def __init__(
        self,
        address,
        simulation,
        state_lock,
        stop_event,
        speed=30,
    ):
        self.simulation = simulation
        self.state_lock = state_lock
        self.stop_event = stop_event

        self.running = True
        self.speed = max(
            1,
            speed,
        )

        super().__init__(
            address,
            self.make_handler(),
        )

    def make_handler(self):
        server = self

        class Handler(
            BaseHTTPRequestHandler
        ):
            def do_GET(self):
                path = urlparse(
                    self.path
                ).path

                if path == "/":
                    body = (
                        DASHBOARD_HTML
                        .encode(
                            "utf-8"
                        )
                    )

                    self.send_response(
                        200
                    )

                    self.send_header(
                        "Content-Type",
                        "text/html; "
                        "charset=utf-8",
                    )

                    self.send_header(
                        "Content-Length",
                        str(
                            len(body)
                        ),
                    )

                    self.end_headers()
                    self.wfile.write(
                        body
                    )

                    return

                if path == "/api/state":
                    with server.state_lock:
                        state = (
                            server.simulation.snapshot(
                                server.running,
                                server.speed,
                            )
                        )

                    body = json.dumps(
                        state,
                        separators=(
                            ",",
                            ":",
                        ),
                    ).encode(
                        "utf-8"
                    )

                    self.send_response(
                        200
                    )

                    self.send_header(
                        "Content-Type",
                        "application/json",
                    )

                    self.send_header(
                        "Cache-Control",
                        "no-store",
                    )

                    self.send_header(
                        "Content-Length",
                        str(
                            len(body)
                        ),
                    )

                    self.end_headers()

                    self.wfile.write(
                        body
                    )

                    return

                self.send_json(
                    404,
                    {
                        "error":
                            "Not found"
                    },
                )

            def send_json(
                self,
                status,
                payload,
            ):
                body = json.dumps(
                    payload
                ).encode(
                    "utf-8"
                )

                self.send_response(
                    status
                )

                self.send_header(
                    "Content-Type",
                    "application/json",
                )

                self.send_header(
                    "Content-Length",
                    str(
                        len(body)
                    ),
                )

                self.end_headers()

                self.wfile.write(
                    body
                )

            def log_message(
                self,
                _format,
                *_args,
            ):
                return

        return Handler


# ---------------------------------------------------------------------------
# Simulation worker
# ---------------------------------------------------------------------------


def simulation_worker(
    server,
):
    while not server.stop_event.is_set():
        with server.state_lock:
            running = server.running
            speed = server.speed

            if running:
                started = (
                    time.perf_counter()
                )

                try:
                    server.simulation.step()

                except Exception as error:
                    # The worker itself should never die because of a
                    # simulation-level exception.
                    server.simulation.add_event(
                        "Simulation recovered "
                        "from internal error: "
                        f"{type(error).__name__}: "
                        f"{error}"
                    )

                elapsed = (
                    time.perf_counter()
                    - started
                )

                delay = max(
                    0.0,
                    (
                        1.0
                        / max(
                            1,
                            speed,
                        )
                    )
                    - elapsed,
                )

            else:
                delay = 0.1

        server.stop_event.wait(
            delay
        )


# ---------------------------------------------------------------------------
# Dashboard
# ---------------------------------------------------------------------------


DASHBOARD_HTML = r"""
<!doctype html>

<html lang="en">

<head>

<meta charset="utf-8">

<meta
    name="viewport"
    content="width=device-width,initial-scale=1"
>

<title>Spatial Void</title>

<style>

:root {
    color-scheme: dark;

    --bg: #080b10;
    --panel: #10161e;
    --line: #222c38;

    --text: #e7edf5;
    --muted: #8d9aaa;

    --green: #76e0ad;
    --blue: #86adff;
}

* {
    box-sizing: border-box;
}

body {
    margin: 0;

    background: var(--bg);
    color: var(--text);

    font:
        14px / 1.45
        system-ui,
        -apple-system,
        BlinkMacSystemFont,
        "Segoe UI",
        sans-serif;
}

main {
    max-width: 1280px;

    margin:
        auto;

    padding:
        28px 20px;
}

h1,
h2 {
    margin: 0;
}

h1 {
    font-size: 25px;
    letter-spacing: -0.02em;
}

h2 {
    font-size: 14px;
    margin-bottom: 14px;
}

.subtitle {
    color: var(--muted);

    margin:
        4px 0 22px;
}

.metrics {
    display: grid;

    grid-template-columns:
        repeat(5, 1fr);

    gap: 10px;

    margin-bottom: 10px;
}

.card,
.panel {
    background: var(--panel);

    border:
        1px solid var(--line);

    border-radius: 10px;
}

.card {
    padding: 14px;
}

.label {
    color: var(--muted);

    font-size: 10px;

    letter-spacing: 0.09em;

    text-transform: uppercase;
}

.value {
    font-size: 23px;

    font-weight: 650;

    margin-top: 2px;
}

.layout {
    display: grid;

    grid-template-columns:
        minmax(0, 1.7fr)
        minmax(320px, 1fr);

    gap: 10px;
}

.panel {
    padding: 15px;

    margin-bottom: 10px;
}

table {
    width: 100%;

    border-collapse:
        collapse;
}

th,
td {
    padding:
        7px 6px;

    border-bottom:
        1px solid var(--line);

    text-align: left;

    white-space: nowrap;
}

th {
    color: var(--muted);

    font-size: 10px;

    letter-spacing: 0.08em;

    text-transform:
        uppercase;
}

td {
    font-size: 12px;
}

.events {
    list-style: none;

    padding: 0;
    margin: 0;

    max-height: 420px;

    overflow: auto;
}

.events li {
    padding: 7px 0;

    border-bottom:
        1px solid var(--line);

    color: #c4cfdb;

    font-size: 12px;
}

.events span {
    color: var(--muted);

    margin-right: 8px;
}

.columns {
    display: grid;

    grid-template-columns:
        1fr 1fr;

    gap: 10px;
}

.bar {
    display: flex;

    gap: 8px;

    align-items:
        center;

    margin: 7px 0;
}

.bar code {
    width: 80px;

    overflow: hidden;

    text-overflow:
        ellipsis;

    color: var(--green);
}

.track {
    flex: 1;

    height: 6px;

    background: #1a222c;

    border-radius:
        99px;

    overflow: hidden;
}

.fill {
    height: 100%;

    background: var(--blue);

    width: 0;
}

@media (max-width: 900px) {
    .metrics {
        grid-template-columns:
            repeat(2, 1fr);
    }

    .layout {
        grid-template-columns:
            1fr;
    }
}

@media (max-width: 560px) {
    main {
        padding:
            18px 12px;
    }

    .metrics {
        grid-template-columns:
            1fr 1fr;
    }

    .columns {
        grid-template-columns:
            1fr;
    }

    th:nth-child(3),
    td:nth-child(3) {
        display: none;
    }
}

</style>

</head>

<body>

<main>

    <h1>Spatial Void</h1>

    <div class="subtitle">
        Autonomous beings evolving biology,
        language, cultural memory and
        executable world-models.
        The dashboard is observational.
    </div>

    <section class="metrics">

        <div class="card">
            <div class="label">
                Cycle
            </div>

            <div
                class="value"
                id="cycle"
            >
                0
            </div>
        </div>

        <div class="card">
            <div class="label">
                Population
            </div>

            <div
                class="value"
                id="population"
            >
                0
            </div>
        </div>

        <div class="card">
            <div class="label">
                Mean Energy
            </div>

            <div
                class="value"
                id="energy"
            >
                0
            </div>
        </div>

        <div class="card">
            <div class="label">
                Vocabulary
            </div>

            <div
                class="value"
                id="vocabulary"
            >
                0
            </div>
        </div>

        <div class="card">
            <div class="label">
                Program Culture
            </div>

            <div
                class="value"
                id="programs"
            >
                0
            </div>
        </div>

    </section>

    <div class="layout">

        <div>

            <section class="panel">

                <h2>
                    Population
                </h2>

                <table>

                    <thead>

                        <tr>
                            <th>Being</th>
                            <th>Gen</th>
                            <th>Position</th>
                            <th>Energy</th>
                            <th>Words</th>
                            <th>Programs</th>
                            <th>Useful Exec</th>
                        </tr>

                    </thead>

                    <tbody id="entities"></tbody>

                </table>

            </section>

            <div class="columns">

                <section class="panel">

                    <h2>
                        Dominant Words
                    </h2>

                    <div id="words"></div>

                </section>

                <section class="panel">

                    <h2>
                        Dominant Programs
                    </h2>

                    <div id="programs-list"></div>

                </section>

            </div>

        </div>

        <div>

            <section class="panel">

                <h2>
                    Evolution Log
                </h2>

                <ul
                    class="events"
                    id="events"
                ></ul>

            </section>

        </div>

    </div>

</main>

<script>

const $ = id =>
    document.getElementById(id);


function renderBars(
    target,
    items,
    key
) {
    target.replaceChildren();

    const max = Math.max(
        1,
        ...items.map(
            x => x.population
        )
    );

    for (
        const item of items
    ) {
        const row =
            document.createElement(
                "div"
            );

        row.className = "bar";

        const label =
            document.createElement(
                "code"
            );

        label.textContent =
            item[key];

        const track =
            document.createElement(
                "div"
            );

        track.className =
            "track";

        const fill =
            document.createElement(
                "div"
            );

        fill.className =
            "fill";

        fill.style.width =
            `${
                (
                    item.population
                    / max
                ) * 100
            }%`;

        track.append(fill);

        row.append(
            label,
            track
        );

        const count =
            document.createElement(
                "span"
            );

        count.textContent =
            item.population;

        count.style.color =
            "var(--muted)";

        row.append(count);

        target.append(row);
    }
}


function render(state) {

    $("cycle").textContent =
        state.cycle.toLocaleString();

    $("population").textContent =
        state.population.toLocaleString();

    $("energy").textContent =
        state.average_energy.toFixed(
            1
        );

    $("vocabulary").textContent =
        state.language_vocabulary.toLocaleString();

    $("programs").textContent =
        state.program_culture.toLocaleString();


    const rows =
        $("entities");

    rows.replaceChildren();


    for (
        const entity of state.entities
    ) {
        const row =
            document.createElement(
                "tr"
            );

        const values = [
            entity.id,
            entity.generation,
            `(${entity.x}, ${entity.y})`,
            entity.energy.toFixed(1),
            entity.words,
            entity.programs,
            entity.useful_programs
        ];


        for (
            const value of values
        ) {
            const cell =
                document.createElement(
                    "td"
                );

            cell.textContent =
                value;

            row.append(cell);
        }


        rows.append(row);
    }


    renderBars(
        $("words"),
        state.dominant_words,
        "word"
    );

    renderBars(
        $("programs-list"),
        state.dominant_programs,
        "program"
    );


    const events =
        $("events");

    events.replaceChildren();


    for (
        const event of state.events
            .slice(0, 40)
    ) {
        const li =
            document.createElement(
                "li"
            );

        const cycle =
            document.createElement(
                "span"
            );

        cycle.textContent =
            `C${event.cycle}`;

        li.append(cycle);

        li.append(
            document.createTextNode(
                event.message
            )
        );

        events.append(li);
    }
}


async function update() {

    try {

        const response =
            await fetch(
                "/api/state",
                {
                    cache:
                        "no-store"
                }
            );

        if (response.ok) {
            render(
                await response.json()
            );
        }

    } catch (_) {
        // Dashboard can tolerate
        // temporary connection failures.
    }
}


setInterval(
    update,
    700
);

update();

</script>

</body>

</html>
"""


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description=(
            "Run the autonomous "
            "Spatial Void experiment."
        )
    )

    parser.add_argument(
        "--port",
        type=int,
        default=8000,
    )

    parser.add_argument(
        "--speed",
        type=int,
        default=30,
        help=(
            "Simulation steps per second."
        ),
    )

    parser.add_argument(
        "--population",
        type=int,
        default=MIN_POPULATION,
    )

    args = parser.parse_args()

    simulation = SpatialVoidSimulation(
        initial_population=(
            args.population
        )
    )

    state_lock = threading.RLock()
    stop_event = threading.Event()

    server = DashboardServer(
        (
            "127.0.0.1",
            args.port,
        ),
        simulation,
        state_lock,
        stop_event,
        speed=max(
            1,
            args.speed,
        ),
    )

    worker = threading.Thread(
        target=simulation_worker,
        args=(server,),
        daemon=True,
        name="simulation_worker",
    )

    worker.start()

    print(
        "Spatial Void running."
    )

    print(
        f"Dashboard: "
        f"http://127.0.0.1:"
        f"{args.port}"
    )

    print(
        "Evolution systems:"
    )

    print(
        "  biological genomes"
    )

    print(
        "  emergent communication"
    )

    print(
        "  cultural language transmission"
    )

    print(
        "  evolving sandboxed programs"
    )

    print(
        "  learned program abstractions"
    )

    print(
        "  cultural selection"
    )

    print(
        "  autonomous environmental modification"
    )

    print(
        "  observer-only dashboard"
    )

    print()

    print(
        "The simulation does not expose "
        "control commands to the beings."
    )

    try:
        server.serve_forever()

    except KeyboardInterrupt:
        print(
            "\nStopping experiment."
        )

    finally:
        stop_event.set()

        server.shutdown()
        server.server_close()

        worker.join(
            timeout=2
        )


if __name__ == "__main__":
    main()