// Lean compiler output
// Module: Lean.Meta.Coe
// Imports: Init Lean.Meta.WHNF Lean.Meta.Transform
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
static lean_object* l_Lean_Meta_isCoeDecl___closed__40;
static lean_object* l_Lean_Meta_isCoeDecl___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_expandCoe___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__45;
size_t l_USize_add(size_t, size_t);
static lean_object* l_Lean_Meta_isCoeDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__17;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__44;
static lean_object* l_Lean_Meta_isCoeDecl___closed__8;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__25;
extern lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__37;
static lean_object* l_Lean_Meta_isCoeDecl___closed__5;
static lean_object* l_Lean_Meta_isCoeDecl___closed__14;
static lean_object* l_Lean_Meta_isCoeDecl___closed__28;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__42;
static lean_object* l_Lean_Meta_isCoeDecl___closed__29;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__3;
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__1;
static lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__2;
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__31;
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__27;
static lean_object* l_Lean_Meta_isCoeDecl___closed__4;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__26;
static lean_object* l_Lean_Meta_isCoeDecl___closed__47;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___boxed(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__34;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__15;
static lean_object* l_Lean_Meta_isCoeDecl___closed__30;
static lean_object* l_Lean_Meta_isCoeDecl___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__23;
static lean_object* l_Lean_Meta_isCoeDecl___closed__41;
static lean_object* l_Lean_Meta_isCoeDecl___closed__24;
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__20;
static lean_object* l_Lean_Meta_isCoeDecl___closed__10;
static lean_object* l_Lean_Meta_isCoeDecl___closed__32;
static lean_object* l_Lean_Meta_isCoeDecl___closed__35;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__16;
static lean_object* l_Lean_Meta_isCoeDecl___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__36;
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_expandCoe___closed__2;
static lean_object* l_Lean_Meta_expandCoe___closed__1;
static lean_object* l_Lean_Meta_isCoeDecl___closed__39;
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__38;
static lean_object* l_Lean_Meta_isCoeDecl___closed__21;
static lean_object* l_Lean_Meta_isCoeDecl___closed__19;
static lean_object* l_Lean_Meta_isCoeDecl___closed__11;
static lean_object* l_Lean_Meta_isCoeDecl___closed__46;
static lean_object* l_Lean_Meta_isCoeDecl___closed__33;
static lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2;
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__22;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__6;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_expandCoe___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__1;
static lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isCoeDecl___closed__43;
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coe");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeB");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeHead");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeTail");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeD");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeTC");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeSort");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Coe");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__18;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeTC");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__21;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeHead");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__24;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeTail");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__27;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeHTCT");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__30;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeDep");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__32;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__33;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeT");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__35;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__36;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__38;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__39;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeSort");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__41;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isCoeDecl___closed__42;
x_2 = l_Lean_Meta_isCoeDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("liftCoeM");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__44;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeM");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isCoeDecl___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isCoeDecl___closed__46;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_isCoeDecl___closed__2;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_isCoeDecl___closed__4;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_isCoeDecl___closed__6;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_isCoeDecl___closed__8;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_isCoeDecl___closed__10;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_isCoeDecl___closed__12;
x_13 = lean_name_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_isCoeDecl___closed__14;
x_15 = lean_name_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_isCoeDecl___closed__16;
x_17 = lean_name_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Meta_isCoeDecl___closed__19;
x_19 = lean_name_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_isCoeDecl___closed__22;
x_21 = lean_name_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_isCoeDecl___closed__25;
x_23 = lean_name_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_isCoeDecl___closed__28;
x_25 = lean_name_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_isCoeDecl___closed__31;
x_27 = lean_name_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_isCoeDecl___closed__34;
x_29 = lean_name_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Meta_isCoeDecl___closed__37;
x_31 = lean_name_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_isCoeDecl___closed__40;
x_33 = lean_name_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_isCoeDecl___closed__43;
x_35 = lean_name_eq(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_isCoeDecl___closed__45;
x_37 = lean_name_eq(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_isCoeDecl___closed__47;
x_39 = lean_name_eq(x_1, x_38);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = 1;
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = 1;
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = 1;
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = 1;
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = 1;
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = 1;
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = 1;
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = 1;
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = 1;
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = 1;
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = 1;
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = 1;
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = 1;
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = 1;
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = 1;
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = 1;
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = 1;
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = 1;
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isCoeDecl(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_getAppFn(x_1);
x_8 = l_Lean_Expr_isConst(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_constName_x21(x_7);
lean_dec(x_7);
x_12 = l_Lean_Meta_isCoeDecl(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_Expr_headBeta(x_24);
x_1 = x_25;
x_6 = x_23;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_apply_6(x_2, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_21, x_6, x_7, x_8, x_9, x_10, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_7);
x_15 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4(x_2, x_3, x_4, x_5, x_14, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_17 = lean_expr_instantiate_rev(x_14, x_5);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = (uint8_t)((x_16 << 24) >> 61);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4___lambda__1), 13, 6);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_15);
x_23 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg(x_13, x_21, x_19, x_22, x_7, x_8, x_9, x_10, x_11, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_expr_instantiate_rev(x_6, x_5);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_28, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 0;
x_33 = 1;
lean_inc(x_8);
x_34 = l_Lean_Meta_mkLambdaFVars(x_5, x_30, x_32, x_33, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_35, x_7, x_8, x_9, x_10, x_11, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_7);
x_15 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5(x_2, x_3, x_4, x_5, x_14, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_17 = lean_expr_instantiate_rev(x_14, x_5);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = (uint8_t)((x_16 << 24) >> 61);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5___lambda__1), 13, 6);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_15);
x_23 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg(x_13, x_21, x_19, x_22, x_7, x_8, x_9, x_10, x_11, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_expr_instantiate_rev(x_6, x_5);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_28, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 0;
x_33 = 1;
lean_inc(x_8);
x_34 = l_Lean_Meta_mkForallFVars(x_5, x_30, x_32, x_33, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_35, x_7, x_8, x_9, x_10, x_11, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_7);
x_15 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6(x_2, x_3, x_4, x_5, x_14, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 8)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_expr_instantiate_rev(x_14, x_5);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_expr_instantiate_rev(x_15, x_5);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_21, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6___lambda__1), 13, 6);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_3);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_16);
x_26 = l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9___rarg(x_13, x_19, x_23, x_25, x_7, x_8, x_9, x_10, x_11, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_expr_instantiate_rev(x_6, x_5);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_35, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 0;
x_40 = 1;
lean_inc(x_8);
x_41 = l_Lean_Meta_mkLambdaFVars(x_5, x_37, x_39, x_40, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_42, x_7, x_8, x_9, x_10, x_11, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_expandCoe___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_7, x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_7, x_6, x_18);
x_20 = x_17;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_6 + x_24;
x_26 = x_22;
x_27 = lean_array_uset(x_19, x_6, x_26);
x_6 = x_25;
x_7 = x_27;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_array_set(x_6, x_7, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_7, x_17);
lean_dec(x_7);
x_5 = x_14;
x_6 = x_16;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_6);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = x_6;
x_26 = lean_box_usize(x_24);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11___boxed__const__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_expandCoe___spec__10___boxed), 13, 7);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_4);
lean_closure_set(x_28, 4, x_26);
lean_closure_set(x_28, 5, x_27);
lean_closure_set(x_28, 6, x_25);
x_29 = x_28;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = lean_apply_6(x_29, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkAppN(x_21, x_31);
x_34 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_33, x_8, x_9, x_10, x_11, x_12, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_11);
x_14 = lean_apply_6(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_apply_6(x_2, x_3, x_5, x_6, x_22, x_8, x_9);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___lambda__1(x_8, x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__2;
x_22 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_21, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg), 7, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
switch (lean_obj_tag(x_14)) {
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_14, x_15);
x_17 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11(x_1, x_2, x_3, x_4, x_14, x_18, x_20, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
case 6:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2;
x_23 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_expandCoe___spec__4(x_1, x_2, x_3, x_4, x_22, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
case 7:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2;
x_25 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_expandCoe___spec__5(x_1, x_2, x_3, x_4, x_24, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2;
x_27 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_expandCoe___spec__6(x_1, x_2, x_3, x_4, x_26, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_27;
}
case 10:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_30, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_expr_update_mdata(x_14, x_32);
x_35 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_34, x_6, x_7, x_8, x_9, x_10, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_14);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
x_42 = lean_ctor_get_uint64(x_14, sizeof(void*)*2);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_41);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_41, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set_uint64(x_46, sizeof(void*)*2, x_42);
x_47 = lean_expr_update_mdata(x_46, x_44);
x_48 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_47, x_6, x_7, x_8, x_9, x_10, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
case 11:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
x_56 = lean_ctor_get(x_14, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_56);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_56, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_expr_update_proj(x_14, x_58);
x_61 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_60, x_6, x_7, x_8, x_9, x_10, x_59);
return x_61;
}
else
{
uint8_t x_62; 
lean_free_object(x_14);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_14, 0);
x_67 = lean_ctor_get(x_14, 1);
x_68 = lean_ctor_get(x_14, 2);
x_69 = lean_ctor_get_uint64(x_14, sizeof(void*)*3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_68);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_1, x_2, x_3, x_4, x_68, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set_uint64(x_73, sizeof(void*)*3, x_69);
x_74 = lean_expr_update_proj(x_73, x_71);
x_75 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_74, x_6, x_7, x_8, x_9, x_10, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
default: 
{
lean_object* x_80; 
x_80 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_expandCoe___spec__3(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_5 = l_Lean_ExprStructEq_instHashableExprStructEq;
x_6 = l_Std_HashMap_insert___rarg(x_4, x_5, x_3, x_1, x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_6);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = lean_apply_7(x_4, lean_box(0), x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_5);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_15, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_13);
lean_inc(x_1);
lean_inc(x_5);
x_18 = lean_apply_1(x_1, x_5);
x_19 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1), 11, 4);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12___rarg), 8, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg(x_21, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__2), 3, 2);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_23);
x_26 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_26, 0, x_6);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_apply_7(x_4, lean_box(0), x_26, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_23);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_23);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_40);
return x_13;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
lean_inc(x_5);
x_43 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_41, x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_1);
lean_inc(x_5);
x_44 = lean_apply_1(x_1, x_5);
x_45 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
lean_inc(x_4);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1), 11, 4);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_2);
lean_closure_set(x_46, 2, x_3);
lean_closure_set(x_46, 3, x_4);
x_47 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_expandCoe___spec__12___rarg), 8, 2);
lean_closure_set(x_47, 0, x_45);
lean_closure_set(x_47, 1, x_46);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg(x_47, x_6, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__2), 3, 2);
lean_closure_set(x_51, 0, x_5);
lean_closure_set(x_51, 1, x_49);
x_52 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_52, 0, x_6);
lean_closure_set(x_52, 1, x_51);
x_53 = lean_apply_7(x_4, lean_box(0), x_52, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_63 = x_48;
} else {
 lean_dec_ref(x_48);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
lean_dec(x_43);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_42);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_13);
if (x_67 == 0)
{
return x_13;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_13, 0);
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_13);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_1(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_box(0);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__1;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__2;
lean_inc(x_7);
lean_inc(x_14);
x_17 = l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2(x_2, x_3, x_9, x_16, x_1, x_14, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_19);
lean_dec(x_7);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe_step), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_expandCoe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_expandCoe___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 3;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_expandCoe___closed__1;
x_12 = l_Lean_Meta_expandCoe___closed__2;
x_13 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(x_1, x_11, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get_uint8(x_8, 0);
x_23 = lean_ctor_get_uint8(x_8, 1);
x_24 = lean_ctor_get_uint8(x_8, 2);
x_25 = lean_ctor_get_uint8(x_8, 3);
x_26 = lean_ctor_get_uint8(x_8, 4);
x_27 = lean_ctor_get_uint8(x_8, 6);
x_28 = lean_ctor_get_uint8(x_8, 7);
x_29 = lean_ctor_get_uint8(x_8, 8);
x_30 = lean_ctor_get_uint8(x_8, 9);
x_31 = lean_ctor_get_uint8(x_8, 10);
x_32 = lean_ctor_get_uint8(x_8, 11);
x_33 = lean_ctor_get_uint8(x_8, 12);
lean_dec(x_8);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_35, 0, x_22);
lean_ctor_set_uint8(x_35, 1, x_23);
lean_ctor_set_uint8(x_35, 2, x_24);
lean_ctor_set_uint8(x_35, 3, x_25);
lean_ctor_set_uint8(x_35, 4, x_26);
lean_ctor_set_uint8(x_35, 5, x_34);
lean_ctor_set_uint8(x_35, 6, x_27);
lean_ctor_set_uint8(x_35, 7, x_28);
lean_ctor_set_uint8(x_35, 8, x_29);
lean_ctor_set_uint8(x_35, 9, x_30);
lean_ctor_set_uint8(x_35, 10, x_31);
lean_ctor_set_uint8(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, 12, x_33);
lean_ctor_set(x_2, 0, x_35);
x_36 = l_Lean_Meta_expandCoe___closed__1;
x_37 = l_Lean_Meta_expandCoe___closed__2;
x_38 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get(x_2, 2);
x_50 = lean_ctor_get(x_2, 3);
x_51 = lean_ctor_get(x_2, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_52 = lean_ctor_get_uint8(x_47, 0);
x_53 = lean_ctor_get_uint8(x_47, 1);
x_54 = lean_ctor_get_uint8(x_47, 2);
x_55 = lean_ctor_get_uint8(x_47, 3);
x_56 = lean_ctor_get_uint8(x_47, 4);
x_57 = lean_ctor_get_uint8(x_47, 6);
x_58 = lean_ctor_get_uint8(x_47, 7);
x_59 = lean_ctor_get_uint8(x_47, 8);
x_60 = lean_ctor_get_uint8(x_47, 9);
x_61 = lean_ctor_get_uint8(x_47, 10);
x_62 = lean_ctor_get_uint8(x_47, 11);
x_63 = lean_ctor_get_uint8(x_47, 12);
if (lean_is_exclusive(x_47)) {
 x_64 = x_47;
} else {
 lean_dec_ref(x_47);
 x_64 = lean_box(0);
}
x_65 = 3;
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 0, 13);
} else {
 x_66 = x_64;
}
lean_ctor_set_uint8(x_66, 0, x_52);
lean_ctor_set_uint8(x_66, 1, x_53);
lean_ctor_set_uint8(x_66, 2, x_54);
lean_ctor_set_uint8(x_66, 3, x_55);
lean_ctor_set_uint8(x_66, 4, x_56);
lean_ctor_set_uint8(x_66, 5, x_65);
lean_ctor_set_uint8(x_66, 6, x_57);
lean_ctor_set_uint8(x_66, 7, x_58);
lean_ctor_set_uint8(x_66, 8, x_59);
lean_ctor_set_uint8(x_66, 9, x_60);
lean_ctor_set_uint8(x_66, 10, x_61);
lean_ctor_set_uint8(x_66, 11, x_62);
lean_ctor_set_uint8(x_66, 12, x_63);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_48);
lean_ctor_set(x_67, 2, x_49);
lean_ctor_set(x_67, 3, x_50);
lean_ctor_set(x_67, 4, x_51);
x_68 = l_Lean_Meta_expandCoe___closed__1;
x_69 = l_Lean_Meta_expandCoe___closed__2;
x_70 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(x_1, x_68, x_69, x_67, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__8(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLetDecl___at_Lean_Meta_expandCoe___spec__9(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_expandCoe___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Meta_expandCoe___spec__10(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_expandCoe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_WHNF(lean_object*);
lean_object* initialize_Lean_Meta_Transform(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Coe(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_isCoeDecl___closed__1 = _init_l_Lean_Meta_isCoeDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__1);
l_Lean_Meta_isCoeDecl___closed__2 = _init_l_Lean_Meta_isCoeDecl___closed__2();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__2);
l_Lean_Meta_isCoeDecl___closed__3 = _init_l_Lean_Meta_isCoeDecl___closed__3();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__3);
l_Lean_Meta_isCoeDecl___closed__4 = _init_l_Lean_Meta_isCoeDecl___closed__4();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__4);
l_Lean_Meta_isCoeDecl___closed__5 = _init_l_Lean_Meta_isCoeDecl___closed__5();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__5);
l_Lean_Meta_isCoeDecl___closed__6 = _init_l_Lean_Meta_isCoeDecl___closed__6();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__6);
l_Lean_Meta_isCoeDecl___closed__7 = _init_l_Lean_Meta_isCoeDecl___closed__7();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__7);
l_Lean_Meta_isCoeDecl___closed__8 = _init_l_Lean_Meta_isCoeDecl___closed__8();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__8);
l_Lean_Meta_isCoeDecl___closed__9 = _init_l_Lean_Meta_isCoeDecl___closed__9();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__9);
l_Lean_Meta_isCoeDecl___closed__10 = _init_l_Lean_Meta_isCoeDecl___closed__10();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__10);
l_Lean_Meta_isCoeDecl___closed__11 = _init_l_Lean_Meta_isCoeDecl___closed__11();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__11);
l_Lean_Meta_isCoeDecl___closed__12 = _init_l_Lean_Meta_isCoeDecl___closed__12();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__12);
l_Lean_Meta_isCoeDecl___closed__13 = _init_l_Lean_Meta_isCoeDecl___closed__13();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__13);
l_Lean_Meta_isCoeDecl___closed__14 = _init_l_Lean_Meta_isCoeDecl___closed__14();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__14);
l_Lean_Meta_isCoeDecl___closed__15 = _init_l_Lean_Meta_isCoeDecl___closed__15();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__15);
l_Lean_Meta_isCoeDecl___closed__16 = _init_l_Lean_Meta_isCoeDecl___closed__16();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__16);
l_Lean_Meta_isCoeDecl___closed__17 = _init_l_Lean_Meta_isCoeDecl___closed__17();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__17);
l_Lean_Meta_isCoeDecl___closed__18 = _init_l_Lean_Meta_isCoeDecl___closed__18();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__18);
l_Lean_Meta_isCoeDecl___closed__19 = _init_l_Lean_Meta_isCoeDecl___closed__19();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__19);
l_Lean_Meta_isCoeDecl___closed__20 = _init_l_Lean_Meta_isCoeDecl___closed__20();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__20);
l_Lean_Meta_isCoeDecl___closed__21 = _init_l_Lean_Meta_isCoeDecl___closed__21();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__21);
l_Lean_Meta_isCoeDecl___closed__22 = _init_l_Lean_Meta_isCoeDecl___closed__22();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__22);
l_Lean_Meta_isCoeDecl___closed__23 = _init_l_Lean_Meta_isCoeDecl___closed__23();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__23);
l_Lean_Meta_isCoeDecl___closed__24 = _init_l_Lean_Meta_isCoeDecl___closed__24();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__24);
l_Lean_Meta_isCoeDecl___closed__25 = _init_l_Lean_Meta_isCoeDecl___closed__25();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__25);
l_Lean_Meta_isCoeDecl___closed__26 = _init_l_Lean_Meta_isCoeDecl___closed__26();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__26);
l_Lean_Meta_isCoeDecl___closed__27 = _init_l_Lean_Meta_isCoeDecl___closed__27();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__27);
l_Lean_Meta_isCoeDecl___closed__28 = _init_l_Lean_Meta_isCoeDecl___closed__28();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__28);
l_Lean_Meta_isCoeDecl___closed__29 = _init_l_Lean_Meta_isCoeDecl___closed__29();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__29);
l_Lean_Meta_isCoeDecl___closed__30 = _init_l_Lean_Meta_isCoeDecl___closed__30();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__30);
l_Lean_Meta_isCoeDecl___closed__31 = _init_l_Lean_Meta_isCoeDecl___closed__31();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__31);
l_Lean_Meta_isCoeDecl___closed__32 = _init_l_Lean_Meta_isCoeDecl___closed__32();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__32);
l_Lean_Meta_isCoeDecl___closed__33 = _init_l_Lean_Meta_isCoeDecl___closed__33();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__33);
l_Lean_Meta_isCoeDecl___closed__34 = _init_l_Lean_Meta_isCoeDecl___closed__34();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__34);
l_Lean_Meta_isCoeDecl___closed__35 = _init_l_Lean_Meta_isCoeDecl___closed__35();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__35);
l_Lean_Meta_isCoeDecl___closed__36 = _init_l_Lean_Meta_isCoeDecl___closed__36();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__36);
l_Lean_Meta_isCoeDecl___closed__37 = _init_l_Lean_Meta_isCoeDecl___closed__37();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__37);
l_Lean_Meta_isCoeDecl___closed__38 = _init_l_Lean_Meta_isCoeDecl___closed__38();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__38);
l_Lean_Meta_isCoeDecl___closed__39 = _init_l_Lean_Meta_isCoeDecl___closed__39();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__39);
l_Lean_Meta_isCoeDecl___closed__40 = _init_l_Lean_Meta_isCoeDecl___closed__40();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__40);
l_Lean_Meta_isCoeDecl___closed__41 = _init_l_Lean_Meta_isCoeDecl___closed__41();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__41);
l_Lean_Meta_isCoeDecl___closed__42 = _init_l_Lean_Meta_isCoeDecl___closed__42();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__42);
l_Lean_Meta_isCoeDecl___closed__43 = _init_l_Lean_Meta_isCoeDecl___closed__43();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__43);
l_Lean_Meta_isCoeDecl___closed__44 = _init_l_Lean_Meta_isCoeDecl___closed__44();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__44);
l_Lean_Meta_isCoeDecl___closed__45 = _init_l_Lean_Meta_isCoeDecl___closed__45();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__45);
l_Lean_Meta_isCoeDecl___closed__46 = _init_l_Lean_Meta_isCoeDecl___closed__46();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__46);
l_Lean_Meta_isCoeDecl___closed__47 = _init_l_Lean_Meta_isCoeDecl___closed__47();
lean_mark_persistent(l_Lean_Meta_isCoeDecl___closed__47);
l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_expandCoe___spec__11___boxed__const__1);
l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__1 = _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__1);
l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__2 = _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_expandCoe___spec__13___rarg___closed__2);
l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__1 = _init_l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__1);
l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2 = _init_l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_transform_visit___at_Lean_Meta_expandCoe___spec__2___lambda__1___closed__2);
l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__1 = _init_l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__1);
l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__2 = _init_l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1___closed__2);
l_Lean_Meta_expandCoe___closed__1 = _init_l_Lean_Meta_expandCoe___closed__1();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__1);
l_Lean_Meta_expandCoe___closed__2 = _init_l_Lean_Meta_expandCoe___closed__2();
lean_mark_persistent(l_Lean_Meta_expandCoe___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
