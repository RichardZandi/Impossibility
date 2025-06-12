// Lean compiler output
// Module: Impossibility.Halting.HaltingWitness
// Imports: Init Impossibility.Evolution Mathlib.Computability.PartrecCode Mathlib.Logic.Encodable.Basic
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
LEAN_EXPORT lean_object* l_HaltingWitness_succCode;
LEAN_EXPORT lean_object* l_HaltingWitness_succDef(lean_object*);
LEAN_EXPORT lean_object* l_HaltingWitness_diagState;
extern lean_object* l_Nat_Partrec_Code_instDenumerable;
LEAN_EXPORT lean_object* l_HaltingWitness_succDef___boxed(lean_object*);
static lean_object* l_HaltingWitness_diagState___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HaltingWitness_succDef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HaltingWitness_succDef___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HaltingWitness_succDef(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_HaltingWitness_succCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
static lean_object* _init_l_HaltingWitness_diagState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_Partrec_Code_instDenumerable;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_HaltingWitness_succCode;
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_HaltingWitness_diagState() {
_start:
{
lean_object* x_1; 
x_1 = l_HaltingWitness_diagState___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_Evolution(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_PartrecCode(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Logic_Encodable_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Impossibility_Halting_HaltingWitness(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_Evolution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_PartrecCode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Logic_Encodable_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HaltingWitness_succCode = _init_l_HaltingWitness_succCode();
lean_mark_persistent(l_HaltingWitness_succCode);
l_HaltingWitness_diagState___closed__1 = _init_l_HaltingWitness_diagState___closed__1();
lean_mark_persistent(l_HaltingWitness_diagState___closed__1);
l_HaltingWitness_diagState = _init_l_HaltingWitness_diagState();
lean_mark_persistent(l_HaltingWitness_diagState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
