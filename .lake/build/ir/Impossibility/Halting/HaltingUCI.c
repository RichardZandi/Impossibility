// Lean compiler output
// Module: Impossibility.Halting.HaltingUCI
// Imports: Init Mathlib.Computability.Primrec Mathlib.Computability.PartrecCode Mathlib.Data.Bool.Basic Godelnumbering.Godel Godelnumbering.Instances Impossibility.Evolution Impossibility.Halting.HaltingWitness UCI.UCICore
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_Primrec(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_PartrecCode(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Bool_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Godel(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_Evolution(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_Halting_HaltingWitness(uint8_t builtin, lean_object*);
lean_object* initialize_UCI_UCICore(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Impossibility_Halting_HaltingUCI(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_Primrec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_PartrecCode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Bool_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Godel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_Evolution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_Halting_HaltingWitness(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UCI_UCICore(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
