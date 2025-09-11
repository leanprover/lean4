// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(uint8_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_State_ctorIdx___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Case_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8;
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Case_ctorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_State_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Case_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Case_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Case_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedFVarId_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(x_1);
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_Search_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 0;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(x_1, x_3);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(x_1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_7 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_7);
x_8 = lean_st_ref_set(x_1, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_st_ref_set(x_1, x_18, x_5);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(x_2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_st_ref_take(x_1, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_11, 2, x_5);
x_17 = lean_st_ref_set(x_1, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Name_num___override(x_8, x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Name_num___override(x_8, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
x_31 = lean_ctor_get(x_11, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_33);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
lean_ctor_set(x_34, 8, x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Name_num___override(x_8, x_9);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_1, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_43, 6);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_43, 7);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_43, 8);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 lean_ctor_release(x_43, 7);
 lean_ctor_release(x_43, 8);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
lean_ctor_set(x_57, 6, x_50);
lean_ctor_set(x_57, 7, x_51);
lean_ctor_set(x_57, 8, x_52);
x_58 = lean_st_ref_set(x_1, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Name_num___override(x_40, x_41);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*22, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get(x_1, 9);
x_14 = lean_ctor_get(x_1, 10);
x_15 = lean_ctor_get(x_1, 11);
x_16 = lean_ctor_get(x_1, 12);
x_17 = lean_ctor_get(x_1, 13);
x_18 = lean_ctor_get(x_1, 14);
x_19 = lean_ctor_get(x_1, 15);
x_20 = lean_ctor_get(x_1, 16);
x_21 = lean_ctor_get(x_1, 17);
x_22 = lean_ctor_get(x_1, 18);
x_23 = lean_ctor_get(x_1, 19);
x_24 = lean_ctor_get(x_1, 20);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*22 + 1);
x_26 = lean_ctor_get(x_1, 21);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set(x_28, 3, x_7);
lean_ctor_set(x_28, 4, x_8);
lean_ctor_set(x_28, 5, x_9);
lean_ctor_set(x_28, 6, x_10);
lean_ctor_set(x_28, 7, x_11);
lean_ctor_set(x_28, 8, x_12);
lean_ctor_set(x_28, 9, x_13);
lean_ctor_set(x_28, 10, x_14);
lean_ctor_set(x_28, 11, x_15);
lean_ctor_set(x_28, 12, x_16);
lean_ctor_set(x_28, 13, x_17);
lean_ctor_set(x_28, 14, x_18);
lean_ctor_set(x_28, 15, x_19);
lean_ctor_set(x_28, 16, x_20);
lean_ctor_set(x_28, 17, x_21);
lean_ctor_set(x_28, 18, x_22);
lean_ctor_set(x_28, 19, x_23);
lean_ctor_set(x_28, 20, x_24);
lean_ctor_set(x_28, 21, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*22, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*22 + 1, x_25);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_4, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_14);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_17);
x_26 = l_Lean_PersistentArray_push___redArg(x_23, x_25);
lean_inc(x_14);
x_27 = l_Lean_FVarIdSet_insert(x_24, x_14);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_26);
x_28 = lean_st_ref_set(x_3, x_20, x_21);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0), 1, 0);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0;
x_32 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_31, x_30, x_4, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_14);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_41);
lean_dec(x_20);
lean_inc(x_14);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_14);
lean_ctor_set(x_44, 2, x_17);
x_45 = l_Lean_PersistentArray_push___redArg(x_41, x_44);
lean_inc(x_14);
x_46 = l_Lean_FVarIdSet_insert(x_43, x_14);
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_42);
x_48 = lean_st_ref_set(x_3, x_47, x_21);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0), 1, 0);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0;
x_52 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_51, x_50, x_4, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_14);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_14);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_mkFreshFVarId___at___Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase);
l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default();
l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind();
l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind);
l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
