#pragma once
/* Registration macros neutralized for the standalone build. */
#define REGISTER_FAMILY(N, ...) struct chg_family_dummy_##N {}
#define REGISTER_HASH(N, ...)   struct chg_hash_dummy_##N {}
