// Lean compiler output
// Module: Impossibility.Totality.TotalityUCI
// Imports: Init Impossibility.UCICoreTest Impossibility.Halting.HaltingUCI Impossibility.EvolutionInstance Mathlib.Computability.PartrecCode Mathlib.Data.Bool.Basic Godelnumbering.Transport Godelnumbering.Godel Godelnumbering.Instances Kleene2.KleeneFix
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
lean_object* l_Nat_Partrec_Code_const(lean_object*);
LEAN_EXPORT lean_object* l_TotalityUCI_goodCode;
static lean_object* l_TotalityUCI_goodCode___closed__1;
static lean_object* _init_l_TotalityUCI_goodCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_Partrec_Code_const(x_1);
return x_2;
}
}
static lean_object* _init_l_TotalityUCI_goodCode() {
_start:
{
lean_object* x_1; 
x_1 = l_TotalityUCI_goodCode___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_UCICoreTest(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_Halting_HaltingUCI(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_EvolutionInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_PartrecCode(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Bool_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Transport(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Godel(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Kleene2_KleeneFix(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Impossibility_Totality_TotalityUCI(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_UCICoreTest(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_Halting_HaltingUCI(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_EvolutionInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_PartrecCode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Bool_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Transport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Godel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Kleene2_KleeneFix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_TotalityUCI_goodCode___closed__1 = _init_l_TotalityUCI_goodCode___closed__1();
lean_mark_persistent(l_TotalityUCI_goodCode___closed__1);
l_TotalityUCI_goodCode = _init_l_TotalityUCI_goodCode();
lean_mark_persistent(l_TotalityUCI_goodCode);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
