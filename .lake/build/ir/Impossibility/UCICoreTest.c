// Lean compiler output
// Module: Impossibility.UCICoreTest
// Imports: Init Mathlib.Computability.PartrecCode Mathlib.Computability.Primrec Mathlib.Data.Bool.Basic Kleene2.KleeneFix Godelnumbering.Transport
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
LEAN_EXPORT lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_b2n(uint8_t);
LEAN_EXPORT lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_b2n___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1;
static lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0___closed__1;
static lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1___closed__1;
LEAN_EXPORT lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0;
static lean_object* _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_Partrec_Code_const(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_Partrec_Code_const(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_b2n(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_b2n___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_b2n(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_PartrecCode(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_Primrec(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Bool_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Kleene2_KleeneFix(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Transport(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Impossibility_UCICoreTest(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_PartrecCode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_Primrec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Bool_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Kleene2_KleeneFix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Transport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0___closed__1 = _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0___closed__1();
lean_mark_persistent(l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0___closed__1);
l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0 = _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0();
lean_mark_persistent(l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code0);
l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1___closed__1 = _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1___closed__1();
lean_mark_persistent(l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1___closed__1);
l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1 = _init_l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1();
lean_mark_persistent(l___private_Impossibility_UCICoreTest_0__Kleene_UCI_Classifier_code1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
