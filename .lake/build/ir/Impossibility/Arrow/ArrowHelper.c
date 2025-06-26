// Lean compiler output
// Module: Impossibility.Arrow.ArrowHelper
// Imports: Init Impossibility.Arrow.ArrowTypes Mathlib.Data.Finset.Basic Mathlib.Data.Finset.Card Mathlib.Tactic Godelnumbering.Godel Mathlib.Data.Bool.Basic Mathlib.Computability.PartrecCode
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
LEAN_EXPORT lean_object* l_ArrowHelper_GoodCode_encode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ArrowHelper_constTrue(lean_object*);
LEAN_EXPORT lean_object* l_ArrowHelper_GoodCode_encode(lean_object*);
LEAN_EXPORT lean_object* l_ArrowHelper_rank___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ArrowHelper_defaultGood___closed__1;
static lean_object* l_ArrowHelper_defaultGood___closed__2;
LEAN_EXPORT lean_object* l_ArrowHelper_outcome(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArrowHelper_defaultGood;
extern lean_object* l_Nat_Partrec_Code_instDenumerable;
LEAN_EXPORT lean_object* l_ArrowHelper_rank(lean_object*);
LEAN_EXPORT lean_object* l_ArrowHelper_outcome___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArrowHelper_outcome___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ArrowHelper_outcome(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ArrowHelper_outcome___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ArrowHelper_rank___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_apply_2(x_3, x_4, x_1);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_2(x_3, x_4, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(2u);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(0u);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_ArrowHelper_rank(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ArrowHelper_rank___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ArrowHelper_constTrue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_ArrowHelper_defaultGood___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_Partrec_Code_const(x_1);
return x_2;
}
}
static lean_object* _init_l_ArrowHelper_defaultGood___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_Partrec_Code_instDenumerable;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_ArrowHelper_defaultGood___closed__1;
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_ArrowHelper_defaultGood() {
_start:
{
lean_object* x_1; 
x_1 = l_ArrowHelper_defaultGood___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ArrowHelper_GoodCode_encode(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ArrowHelper_GoodCode_encode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ArrowHelper_GoodCode_encode(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Impossibility_Arrow_ArrowTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Card(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Godelnumbering_Godel(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Bool_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_PartrecCode(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Impossibility_Arrow_ArrowHelper(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Impossibility_Arrow_ArrowTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Card(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Godelnumbering_Godel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Bool_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_PartrecCode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ArrowHelper_defaultGood___closed__1 = _init_l_ArrowHelper_defaultGood___closed__1();
lean_mark_persistent(l_ArrowHelper_defaultGood___closed__1);
l_ArrowHelper_defaultGood___closed__2 = _init_l_ArrowHelper_defaultGood___closed__2();
lean_mark_persistent(l_ArrowHelper_defaultGood___closed__2);
l_ArrowHelper_defaultGood = _init_l_ArrowHelper_defaultGood();
lean_mark_persistent(l_ArrowHelper_defaultGood);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
