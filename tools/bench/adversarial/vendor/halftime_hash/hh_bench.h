#pragma once
/* Single include for the benchmark harness. Applies the AArch64 naming fix
 * (see arm_neon_fix.h) then pulls in the verbatim upstream header, exposing
 * namespace halftime_hash unchanged. Use halftime_hash::HalftimeHashStyle512.
 *
 * Entropy: allocate kEntropyBytesNeeded (70928 bytes = 8866 uint64 words) and
 * fill every word with random bits before hashing; the same entropy buffer is
 * reused for all inputs. */
#include "arm_neon_fix.h"
#include "halftime-hash.hpp"
