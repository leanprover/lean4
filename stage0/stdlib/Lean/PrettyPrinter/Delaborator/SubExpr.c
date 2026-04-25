// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.SubExpr
// Imports: public import Lean.SubExpr
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
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_maxChildren;
extern lean_object* l_Lean_SubExpr_Pos_typeCoord;
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withProj"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withMDataExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withLetVarType"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withLetValue"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withLetBody"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0(lean_object* v_o_4_, lean_object* v_k_5_, lean_object* v_v_6_){
_start:
{
lean_object* v_map_7_; uint8_t v_hasTrace_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v_map_7_ = lean_ctor_get(v_o_4_, 0);
v_hasTrace_8_ = lean_ctor_get_uint8(v_o_4_, sizeof(void*)*1);
v_isSharedCheck_21_ = !lean_is_exclusive(v_o_4_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v_o_4_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_map_7_);
lean_dec(v_o_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; 
lean_inc(v_k_5_);
v___x_12_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_5_, v_v_6_, v_map_7_);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1));
v___x_14_ = l_Lean_Name_isPrefixOf(v___x_13_, v_k_5_);
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_12_);
v___x_16_ = v___x_10_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_12_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_14_);
return v___x_16_;
}
}
else
{
lean_object* v___x_19_; 
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_12_);
v___x_19_ = v___x_10_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_20_, sizeof(void*)*1, v_hasTrace_8_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(lean_object* v_k_22_, lean_object* v_v_23_, lean_object* v_t_24_){
_start:
{
if (lean_obj_tag(v_t_24_) == 0)
{
lean_object* v_size_25_; lean_object* v_k_26_; lean_object* v_v_27_; lean_object* v_l_28_; lean_object* v_r_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_310_; 
v_size_25_ = lean_ctor_get(v_t_24_, 0);
v_k_26_ = lean_ctor_get(v_t_24_, 1);
v_v_27_ = lean_ctor_get(v_t_24_, 2);
v_l_28_ = lean_ctor_get(v_t_24_, 3);
v_r_29_ = lean_ctor_get(v_t_24_, 4);
v_isSharedCheck_310_ = !lean_is_exclusive(v_t_24_);
if (v_isSharedCheck_310_ == 0)
{
v___x_31_ = v_t_24_;
v_isShared_32_ = v_isSharedCheck_310_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_r_29_);
lean_inc(v_l_28_);
lean_inc(v_v_27_);
lean_inc(v_k_26_);
lean_inc(v_size_25_);
lean_dec(v_t_24_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_310_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
uint8_t v___x_33_; 
v___x_33_ = lean_nat_dec_lt(v_k_22_, v_k_26_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; 
v___x_34_ = lean_nat_dec_eq(v_k_22_, v_k_26_);
if (v___x_34_ == 0)
{
lean_object* v_impl_35_; lean_object* v___x_36_; 
lean_dec(v_size_25_);
v_impl_35_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_22_, v_v_23_, v_r_29_);
v___x_36_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_28_) == 0)
{
lean_object* v_size_37_; lean_object* v_size_38_; lean_object* v_k_39_; lean_object* v_v_40_; lean_object* v_l_41_; lean_object* v_r_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_size_37_ = lean_ctor_get(v_l_28_, 0);
v_size_38_ = lean_ctor_get(v_impl_35_, 0);
lean_inc(v_size_38_);
v_k_39_ = lean_ctor_get(v_impl_35_, 1);
lean_inc(v_k_39_);
v_v_40_ = lean_ctor_get(v_impl_35_, 2);
lean_inc(v_v_40_);
v_l_41_ = lean_ctor_get(v_impl_35_, 3);
lean_inc(v_l_41_);
v_r_42_ = lean_ctor_get(v_impl_35_, 4);
lean_inc(v_r_42_);
v___x_43_ = lean_unsigned_to_nat(3u);
v___x_44_ = lean_nat_mul(v___x_43_, v_size_37_);
v___x_45_ = lean_nat_dec_lt(v___x_44_, v_size_38_);
lean_dec(v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
lean_dec(v_r_42_);
lean_dec(v_l_41_);
lean_dec(v_v_40_);
lean_dec(v_k_39_);
v___x_46_ = lean_nat_add(v___x_36_, v_size_37_);
v___x_47_ = lean_nat_add(v___x_46_, v_size_38_);
lean_dec(v_size_38_);
lean_dec(v___x_46_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v_impl_35_);
lean_ctor_set(v___x_31_, 0, v___x_47_);
v___x_49_ = v___x_31_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_50_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_50_, 3, v_l_28_);
lean_ctor_set(v_reuseFailAlloc_50_, 4, v_impl_35_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
else
{
lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_114_; 
v_isSharedCheck_114_ = !lean_is_exclusive(v_impl_35_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; lean_object* v_unused_117_; lean_object* v_unused_118_; lean_object* v_unused_119_; 
v_unused_115_ = lean_ctor_get(v_impl_35_, 4);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v_impl_35_, 3);
lean_dec(v_unused_116_);
v_unused_117_ = lean_ctor_get(v_impl_35_, 2);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_impl_35_, 1);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_impl_35_, 0);
lean_dec(v_unused_119_);
v___x_52_ = v_impl_35_;
v_isShared_53_ = v_isSharedCheck_114_;
goto v_resetjp_51_;
}
else
{
lean_dec(v_impl_35_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_114_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_size_54_; lean_object* v_k_55_; lean_object* v_v_56_; lean_object* v_l_57_; lean_object* v_r_58_; lean_object* v_size_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_size_54_ = lean_ctor_get(v_l_41_, 0);
v_k_55_ = lean_ctor_get(v_l_41_, 1);
v_v_56_ = lean_ctor_get(v_l_41_, 2);
v_l_57_ = lean_ctor_get(v_l_41_, 3);
v_r_58_ = lean_ctor_get(v_l_41_, 4);
v_size_59_ = lean_ctor_get(v_r_42_, 0);
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_nat_mul(v___x_60_, v_size_59_);
v___x_62_ = lean_nat_dec_lt(v_size_54_, v___x_61_);
lean_dec(v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_90_; 
lean_inc(v_r_58_);
lean_inc(v_l_57_);
lean_inc(v_v_56_);
lean_inc(v_k_55_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_l_41_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; lean_object* v_unused_94_; lean_object* v_unused_95_; 
v_unused_91_ = lean_ctor_get(v_l_41_, 4);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_l_41_, 3);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_l_41_, 2);
lean_dec(v_unused_93_);
v_unused_94_ = lean_ctor_get(v_l_41_, 1);
lean_dec(v_unused_94_);
v_unused_95_ = lean_ctor_get(v_l_41_, 0);
lean_dec(v_unused_95_);
v___x_64_ = v_l_41_;
v_isShared_65_ = v_isSharedCheck_90_;
goto v_resetjp_63_;
}
else
{
lean_dec(v_l_41_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_90_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___y_69_; lean_object* v___y_70_; lean_object* v___y_71_; lean_object* v___y_80_; 
v___x_66_ = lean_nat_add(v___x_36_, v_size_37_);
v___x_67_ = lean_nat_add(v___x_66_, v_size_38_);
lean_dec(v_size_38_);
if (lean_obj_tag(v_l_57_) == 0)
{
lean_object* v_size_88_; 
v_size_88_ = lean_ctor_get(v_l_57_, 0);
lean_inc(v_size_88_);
v___y_80_ = v_size_88_;
goto v___jp_79_;
}
else
{
lean_object* v___x_89_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___y_80_ = v___x_89_;
goto v___jp_79_;
}
v___jp_68_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_nat_add(v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec(v___y_70_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_r_42_);
lean_ctor_set(v___x_64_, 3, v_r_58_);
lean_ctor_set(v___x_64_, 2, v_v_40_);
lean_ctor_set(v___x_64_, 1, v_k_39_);
lean_ctor_set(v___x_64_, 0, v___x_72_);
v___x_74_ = v___x_64_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_k_39_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v_v_40_);
lean_ctor_set(v_reuseFailAlloc_78_, 3, v_r_58_);
lean_ctor_set(v_reuseFailAlloc_78_, 4, v_r_42_);
v___x_74_ = v_reuseFailAlloc_78_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_76_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 4, v___x_74_);
lean_ctor_set(v___x_52_, 3, v___y_69_);
lean_ctor_set(v___x_52_, 2, v_v_56_);
lean_ctor_set(v___x_52_, 1, v_k_55_);
lean_ctor_set(v___x_52_, 0, v___x_67_);
v___x_76_ = v___x_52_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_k_55_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v_v_56_);
lean_ctor_set(v_reuseFailAlloc_77_, 3, v___y_69_);
lean_ctor_set(v_reuseFailAlloc_77_, 4, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_nat_add(v___x_66_, v___y_80_);
lean_dec(v___y_80_);
lean_dec(v___x_66_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v_l_57_);
lean_ctor_set(v___x_31_, 0, v___x_81_);
v___x_83_ = v___x_31_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_87_, 3, v_l_28_);
lean_ctor_set(v_reuseFailAlloc_87_, 4, v_l_57_);
v___x_83_ = v_reuseFailAlloc_87_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; 
v___x_84_ = lean_nat_add(v___x_36_, v_size_59_);
if (lean_obj_tag(v_r_58_) == 0)
{
lean_object* v_size_85_; 
v_size_85_ = lean_ctor_get(v_r_58_, 0);
lean_inc(v_size_85_);
v___y_69_ = v___x_83_;
v___y_70_ = v___x_84_;
v___y_71_ = v_size_85_;
goto v___jp_68_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___y_69_ = v___x_83_;
v___y_70_ = v___x_84_;
v___y_71_ = v___x_86_;
goto v___jp_68_;
}
}
}
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
lean_del_object(v___x_31_);
v___x_96_ = lean_nat_add(v___x_36_, v_size_37_);
v___x_97_ = lean_nat_add(v___x_96_, v_size_38_);
lean_dec(v_size_38_);
v___x_98_ = lean_nat_add(v___x_96_, v_size_54_);
lean_dec(v___x_96_);
lean_inc_ref(v_l_28_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 4, v_l_41_);
lean_ctor_set(v___x_52_, 3, v_l_28_);
lean_ctor_set(v___x_52_, 2, v_v_27_);
lean_ctor_set(v___x_52_, 1, v_k_26_);
lean_ctor_set(v___x_52_, 0, v___x_98_);
v___x_100_ = v___x_52_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_l_28_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_l_41_);
v___x_100_ = v_reuseFailAlloc_113_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_isSharedCheck_107_ = !lean_is_exclusive(v_l_28_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_108_ = lean_ctor_get(v_l_28_, 4);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_l_28_, 3);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_l_28_, 2);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_l_28_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_l_28_, 0);
lean_dec(v_unused_112_);
v___x_102_ = v_l_28_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_l_28_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 4, v_r_42_);
lean_ctor_set(v___x_102_, 3, v___x_100_);
lean_ctor_set(v___x_102_, 2, v_v_40_);
lean_ctor_set(v___x_102_, 1, v_k_39_);
lean_ctor_set(v___x_102_, 0, v___x_97_);
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_k_39_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_v_40_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_r_42_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_120_; 
v_l_120_ = lean_ctor_get(v_impl_35_, 3);
lean_inc(v_l_120_);
if (lean_obj_tag(v_l_120_) == 0)
{
lean_object* v_r_121_; lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_146_; 
v_r_121_ = lean_ctor_get(v_impl_35_, 4);
v_k_122_ = lean_ctor_get(v_impl_35_, 1);
v_v_123_ = lean_ctor_get(v_impl_35_, 2);
v_isSharedCheck_146_ = !lean_is_exclusive(v_impl_35_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; lean_object* v_unused_148_; 
v_unused_147_ = lean_ctor_get(v_impl_35_, 3);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_impl_35_, 0);
lean_dec(v_unused_148_);
v___x_125_ = v_impl_35_;
v_isShared_126_ = v_isSharedCheck_146_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_r_121_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
lean_dec(v_impl_35_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_146_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_142_; 
v_k_127_ = lean_ctor_get(v_l_120_, 1);
v_v_128_ = lean_ctor_get(v_l_120_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_l_120_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; lean_object* v_unused_144_; lean_object* v_unused_145_; 
v_unused_143_ = lean_ctor_get(v_l_120_, 4);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_l_120_, 3);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_l_120_, 0);
lean_dec(v_unused_145_);
v___x_130_ = v_l_120_;
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_v_128_);
lean_inc(v_k_127_);
lean_dec(v_l_120_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_121_, 2);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v_r_121_);
lean_ctor_set(v___x_130_, 3, v_r_121_);
lean_ctor_set(v___x_130_, 2, v_v_27_);
lean_ctor_set(v___x_130_, 1, v_k_26_);
lean_ctor_set(v___x_130_, 0, v___x_36_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_r_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_r_121_);
v___x_134_ = v_reuseFailAlloc_141_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
lean_inc(v_r_121_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 3, v_r_121_);
lean_ctor_set(v___x_125_, 0, v___x_36_);
v___x_136_ = v___x_125_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_r_121_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_r_121_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v___x_136_);
lean_ctor_set(v___x_31_, 3, v___x_134_);
lean_ctor_set(v___x_31_, 2, v_v_128_);
lean_ctor_set(v___x_31_, 1, v_k_127_);
lean_ctor_set(v___x_31_, 0, v___x_132_);
v___x_138_ = v___x_31_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
else
{
lean_object* v_r_149_; 
v_r_149_ = lean_ctor_get(v_impl_35_, 4);
lean_inc(v_r_149_);
if (lean_obj_tag(v_r_149_) == 0)
{
lean_object* v_k_150_; lean_object* v_v_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_162_; 
v_k_150_ = lean_ctor_get(v_impl_35_, 1);
v_v_151_ = lean_ctor_get(v_impl_35_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_impl_35_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; 
v_unused_163_ = lean_ctor_get(v_impl_35_, 4);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_impl_35_, 3);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_impl_35_, 0);
lean_dec(v_unused_165_);
v___x_153_ = v_impl_35_;
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_v_151_);
lean_inc(v_k_150_);
lean_dec(v_impl_35_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(3u);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_l_120_);
lean_ctor_set(v___x_153_, 2, v_v_27_);
lean_ctor_set(v___x_153_, 1, v_k_26_);
lean_ctor_set(v___x_153_, 0, v___x_36_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v_l_120_);
lean_ctor_set(v_reuseFailAlloc_161_, 4, v_l_120_);
v___x_157_ = v_reuseFailAlloc_161_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v_r_149_);
lean_ctor_set(v___x_31_, 3, v___x_157_);
lean_ctor_set(v___x_31_, 2, v_v_151_);
lean_ctor_set(v___x_31_, 1, v_k_150_);
lean_ctor_set(v___x_31_, 0, v___x_155_);
v___x_159_ = v___x_31_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_k_150_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_v_151_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v_r_149_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(2u);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v_impl_35_);
lean_ctor_set(v___x_31_, 3, v_r_149_);
lean_ctor_set(v___x_31_, 0, v___x_166_);
v___x_168_ = v___x_31_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_r_149_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_impl_35_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
else
{
lean_object* v___x_171_; 
lean_dec(v_v_27_);
lean_dec(v_k_26_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 2, v_v_23_);
lean_ctor_set(v___x_31_, 1, v_k_22_);
v___x_171_ = v___x_31_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_25_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_22_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_23_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_28_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_r_29_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v_impl_173_; lean_object* v___x_174_; 
lean_dec(v_size_25_);
v_impl_173_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_22_, v_v_23_, v_l_28_);
v___x_174_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_29_) == 0)
{
lean_object* v_size_175_; lean_object* v_size_176_; lean_object* v_k_177_; lean_object* v_v_178_; lean_object* v_l_179_; lean_object* v_r_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_size_175_ = lean_ctor_get(v_r_29_, 0);
v_size_176_ = lean_ctor_get(v_impl_173_, 0);
lean_inc(v_size_176_);
v_k_177_ = lean_ctor_get(v_impl_173_, 1);
lean_inc(v_k_177_);
v_v_178_ = lean_ctor_get(v_impl_173_, 2);
lean_inc(v_v_178_);
v_l_179_ = lean_ctor_get(v_impl_173_, 3);
lean_inc(v_l_179_);
v_r_180_ = lean_ctor_get(v_impl_173_, 4);
lean_inc(v_r_180_);
v___x_181_ = lean_unsigned_to_nat(3u);
v___x_182_ = lean_nat_mul(v___x_181_, v_size_175_);
v___x_183_ = lean_nat_dec_lt(v___x_182_, v_size_176_);
lean_dec(v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec(v_r_180_);
lean_dec(v_l_179_);
lean_dec(v_v_178_);
lean_dec(v_k_177_);
v___x_184_ = lean_nat_add(v___x_174_, v_size_176_);
lean_dec(v_size_176_);
v___x_185_ = lean_nat_add(v___x_184_, v_size_175_);
lean_dec(v___x_184_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 3, v_impl_173_);
lean_ctor_set(v___x_31_, 0, v___x_185_);
v___x_187_ = v___x_31_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_impl_173_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v_r_29_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_254_; 
v_isSharedCheck_254_ = !lean_is_exclusive(v_impl_173_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_255_ = lean_ctor_get(v_impl_173_, 4);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_impl_173_, 3);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_impl_173_, 2);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_impl_173_, 1);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_impl_173_, 0);
lean_dec(v_unused_259_);
v___x_190_ = v_impl_173_;
v_isShared_191_ = v_isSharedCheck_254_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_impl_173_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_254_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_size_192_; lean_object* v_size_193_; lean_object* v_k_194_; lean_object* v_v_195_; lean_object* v_l_196_; lean_object* v_r_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_size_192_ = lean_ctor_get(v_l_179_, 0);
v_size_193_ = lean_ctor_get(v_r_180_, 0);
v_k_194_ = lean_ctor_get(v_r_180_, 1);
v_v_195_ = lean_ctor_get(v_r_180_, 2);
v_l_196_ = lean_ctor_get(v_r_180_, 3);
v_r_197_ = lean_ctor_get(v_r_180_, 4);
v___x_198_ = lean_unsigned_to_nat(2u);
v___x_199_ = lean_nat_mul(v___x_198_, v_size_192_);
v___x_200_ = lean_nat_dec_lt(v_size_193_, v___x_199_);
lean_dec(v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_229_; 
lean_inc(v_r_197_);
lean_inc(v_l_196_);
lean_inc(v_v_195_);
lean_inc(v_k_194_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_r_180_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_230_ = lean_ctor_get(v_r_180_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_r_180_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_r_180_, 2);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_r_180_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_r_180_, 0);
lean_dec(v_unused_234_);
v___x_202_ = v_r_180_;
v_isShared_203_ = v_isSharedCheck_229_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_r_180_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_229_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___x_217_; lean_object* v___y_219_; 
v___x_204_ = lean_nat_add(v___x_174_, v_size_176_);
lean_dec(v_size_176_);
v___x_205_ = lean_nat_add(v___x_204_, v_size_175_);
lean_dec(v___x_204_);
v___x_217_ = lean_nat_add(v___x_174_, v_size_192_);
if (lean_obj_tag(v_l_196_) == 0)
{
lean_object* v_size_227_; 
v_size_227_ = lean_ctor_get(v_l_196_, 0);
lean_inc(v_size_227_);
v___y_219_ = v_size_227_;
goto v___jp_218_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___y_219_ = v___x_228_;
goto v___jp_218_;
}
v___jp_206_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_nat_add(v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 4, v_r_29_);
lean_ctor_set(v___x_202_, 3, v_r_197_);
lean_ctor_set(v___x_202_, 2, v_v_27_);
lean_ctor_set(v___x_202_, 1, v_k_26_);
lean_ctor_set(v___x_202_, 0, v___x_210_);
v___x_212_ = v___x_202_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_r_197_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_r_29_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v___x_212_);
lean_ctor_set(v___x_190_, 3, v___y_207_);
lean_ctor_set(v___x_190_, 2, v_v_195_);
lean_ctor_set(v___x_190_, 1, v_k_194_);
lean_ctor_set(v___x_190_, 0, v___x_205_);
v___x_214_ = v___x_190_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_194_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_195_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v___y_207_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_nat_add(v___x_217_, v___y_219_);
lean_dec(v___y_219_);
lean_dec(v___x_217_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v_l_196_);
lean_ctor_set(v___x_31_, 3, v_l_179_);
lean_ctor_set(v___x_31_, 2, v_v_178_);
lean_ctor_set(v___x_31_, 1, v_k_177_);
lean_ctor_set(v___x_31_, 0, v___x_220_);
v___x_222_ = v___x_31_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_k_177_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_v_178_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_l_179_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_l_196_);
v___x_222_ = v_reuseFailAlloc_226_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_nat_add(v___x_174_, v_size_175_);
if (lean_obj_tag(v_r_197_) == 0)
{
lean_object* v_size_224_; 
v_size_224_ = lean_ctor_get(v_r_197_, 0);
lean_inc(v_size_224_);
v___y_207_ = v___x_222_;
v___y_208_ = v___x_223_;
v___y_209_ = v_size_224_;
goto v___jp_206_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___y_207_ = v___x_222_;
v___y_208_ = v___x_223_;
v___y_209_ = v___x_225_;
goto v___jp_206_;
}
}
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_del_object(v___x_31_);
v___x_235_ = lean_nat_add(v___x_174_, v_size_176_);
lean_dec(v_size_176_);
v___x_236_ = lean_nat_add(v___x_235_, v_size_175_);
lean_dec(v___x_235_);
v___x_237_ = lean_nat_add(v___x_174_, v_size_175_);
v___x_238_ = lean_nat_add(v___x_237_, v_size_193_);
lean_dec(v___x_237_);
lean_inc_ref(v_r_29_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v_r_29_);
lean_ctor_set(v___x_190_, 3, v_r_180_);
lean_ctor_set(v___x_190_, 2, v_v_27_);
lean_ctor_set(v___x_190_, 1, v_k_26_);
lean_ctor_set(v___x_190_, 0, v___x_238_);
v___x_240_ = v___x_190_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_r_180_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_r_29_);
v___x_240_ = v_reuseFailAlloc_253_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_isSharedCheck_247_ = !lean_is_exclusive(v_r_29_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; lean_object* v_unused_251_; lean_object* v_unused_252_; 
v_unused_248_ = lean_ctor_get(v_r_29_, 4);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_r_29_, 3);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_r_29_, 2);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_r_29_, 1);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_r_29_, 0);
lean_dec(v_unused_252_);
v___x_242_ = v_r_29_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_r_29_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v___x_240_);
lean_ctor_set(v___x_242_, 3, v_l_179_);
lean_ctor_set(v___x_242_, 2, v_v_178_);
lean_ctor_set(v___x_242_, 1, v_k_177_);
lean_ctor_set(v___x_242_, 0, v___x_236_);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_k_177_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_v_178_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_l_179_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v___x_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_260_; 
v_l_260_ = lean_ctor_get(v_impl_173_, 3);
lean_inc(v_l_260_);
if (lean_obj_tag(v_l_260_) == 0)
{
lean_object* v_r_261_; lean_object* v_k_262_; lean_object* v_v_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_274_; 
v_r_261_ = lean_ctor_get(v_impl_173_, 4);
v_k_262_ = lean_ctor_get(v_impl_173_, 1);
v_v_263_ = lean_ctor_get(v_impl_173_, 2);
v_isSharedCheck_274_ = !lean_is_exclusive(v_impl_173_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_275_ = lean_ctor_get(v_impl_173_, 3);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_impl_173_, 0);
lean_dec(v_unused_276_);
v___x_265_ = v_impl_173_;
v_isShared_266_ = v_isSharedCheck_274_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_r_261_);
lean_inc(v_v_263_);
lean_inc(v_k_262_);
lean_dec(v_impl_173_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_274_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_261_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 3, v_r_261_);
lean_ctor_set(v___x_265_, 2, v_v_27_);
lean_ctor_set(v___x_265_, 1, v_k_26_);
lean_ctor_set(v___x_265_, 0, v___x_174_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_r_261_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_r_261_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_271_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v___x_269_);
lean_ctor_set(v___x_31_, 3, v_l_260_);
lean_ctor_set(v___x_31_, 2, v_v_263_);
lean_ctor_set(v___x_31_, 1, v_k_262_);
lean_ctor_set(v___x_31_, 0, v___x_267_);
v___x_271_ = v___x_31_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_k_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_v_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_l_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_r_277_; 
v_r_277_ = lean_ctor_get(v_impl_173_, 4);
lean_inc(v_r_277_);
if (lean_obj_tag(v_r_277_) == 0)
{
lean_object* v_k_278_; lean_object* v_v_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_302_; 
v_k_278_ = lean_ctor_get(v_impl_173_, 1);
v_v_279_ = lean_ctor_get(v_impl_173_, 2);
v_isSharedCheck_302_ = !lean_is_exclusive(v_impl_173_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_303_ = lean_ctor_get(v_impl_173_, 4);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_impl_173_, 3);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_impl_173_, 0);
lean_dec(v_unused_305_);
v___x_281_ = v_impl_173_;
v_isShared_282_ = v_isSharedCheck_302_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_v_279_);
lean_inc(v_k_278_);
lean_dec(v_impl_173_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_302_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_k_283_; lean_object* v_v_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_298_; 
v_k_283_ = lean_ctor_get(v_r_277_, 1);
v_v_284_ = lean_ctor_get(v_r_277_, 2);
v_isSharedCheck_298_ = !lean_is_exclusive(v_r_277_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_299_ = lean_ctor_get(v_r_277_, 4);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_r_277_, 3);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_r_277_, 0);
lean_dec(v_unused_301_);
v___x_286_ = v_r_277_;
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_v_284_);
lean_inc(v_k_283_);
lean_dec(v_r_277_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(3u);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 4, v_l_260_);
lean_ctor_set(v___x_286_, 3, v_l_260_);
lean_ctor_set(v___x_286_, 2, v_v_279_);
lean_ctor_set(v___x_286_, 1, v_k_278_);
lean_ctor_set(v___x_286_, 0, v___x_174_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_k_278_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_v_279_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_l_260_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_l_260_);
v___x_290_ = v_reuseFailAlloc_297_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_292_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 4, v_l_260_);
lean_ctor_set(v___x_281_, 2, v_v_27_);
lean_ctor_set(v___x_281_, 1, v_k_26_);
lean_ctor_set(v___x_281_, 0, v___x_174_);
v___x_292_ = v___x_281_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_l_260_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_l_260_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v___x_292_);
lean_ctor_set(v___x_31_, 3, v___x_290_);
lean_ctor_set(v___x_31_, 2, v_v_284_);
lean_ctor_set(v___x_31_, 1, v_k_283_);
lean_ctor_set(v___x_31_, 0, v___x_288_);
v___x_294_ = v___x_31_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_k_283_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_v_284_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_unsigned_to_nat(2u);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 4, v_r_277_);
lean_ctor_set(v___x_31_, 3, v_impl_173_);
lean_ctor_set(v___x_31_, 0, v___x_306_);
v___x_308_ = v___x_31_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_impl_173_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_r_277_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_k_22_);
lean_ctor_set(v___x_312_, 2, v_v_23_);
lean_ctor_set(v___x_312_, 3, v_t_24_);
lean_ctor_set(v___x_312_, 4, v_t_24_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(lean_object* v_t_313_, lean_object* v_k_314_){
_start:
{
if (lean_obj_tag(v_t_313_) == 0)
{
lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v_l_317_; lean_object* v_r_318_; uint8_t v___x_319_; 
v_k_315_ = lean_ctor_get(v_t_313_, 1);
v_v_316_ = lean_ctor_get(v_t_313_, 2);
v_l_317_ = lean_ctor_get(v_t_313_, 3);
v_r_318_ = lean_ctor_get(v_t_313_, 4);
v___x_319_ = lean_nat_dec_lt(v_k_314_, v_k_315_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_eq(v_k_314_, v_k_315_);
if (v___x_320_ == 0)
{
v_t_313_ = v_r_318_;
goto _start;
}
else
{
lean_object* v___x_322_; 
lean_inc(v_v_316_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v_v_316_);
return v___x_322_;
}
}
else
{
v_t_313_ = v_l_317_;
goto _start;
}
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg___boxed(lean_object* v_t_325_, lean_object* v_k_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_t_325_, v_k_326_);
lean_dec(v_k_326_);
lean_dec(v_t_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt(lean_object* v_optionsPerPos_328_, lean_object* v_pos_329_, lean_object* v_name_330_, lean_object* v_value_331_){
_start:
{
lean_object* v___y_333_; lean_object* v___x_336_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_optionsPerPos_328_, v_pos_329_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Options_empty;
v___y_333_ = v___x_337_;
goto v___jp_332_;
}
else
{
lean_object* v_val_338_; 
v_val_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_val_338_);
lean_dec_ref(v___x_336_);
v___y_333_ = v_val_338_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0(v___y_333_, v_name_330_, v_value_331_);
v___x_335_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_pos_329_, v___x_334_, v_optionsPerPos_328_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1(lean_object* v_00_u03b2_339_, lean_object* v_k_340_, lean_object* v_v_341_, lean_object* v_t_342_, lean_object* v_hl_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_340_, v_v_341_, v_t_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(lean_object* v_00_u03b4_345_, lean_object* v_t_346_, lean_object* v_k_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_t_346_, v_k_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___boxed(lean_object* v_00_u03b4_349_, lean_object* v_t_350_, lean_object* v_k_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(v_00_u03b4_349_, v_t_350_, v_k_351_);
lean_dec(v_k_351_);
lean_dec(v_t_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(lean_object* v_b_u2082_353_, lean_object* v___f_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v___f_354_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_b_u2082_353_);
return v___x_356_;
}
else
{
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_val_357_ = lean_ctor_get(v_x_355_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_355_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v_x_355_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v_x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = l_Lean_Options_mergeBy(v___f_354_, v_val_357_, v_b_u2082_353_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_dv_368_){
_start:
{
lean_inc_ref(v_dv_368_);
return v_dv_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed(lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_dv_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0(v_x_369_, v_x_370_, v_dv_371_);
lean_dec_ref(v_dv_371_);
lean_dec_ref(v_x_370_);
lean_dec(v_x_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(lean_object* v_b_u2082_374_, lean_object* v_k_375_, lean_object* v_t_376_){
_start:
{
lean_object* v___f_377_; 
v___f_377_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0));
if (lean_obj_tag(v_t_376_) == 0)
{
lean_object* v_size_378_; lean_object* v_k_379_; lean_object* v_v_380_; lean_object* v_l_381_; lean_object* v_r_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_398_; 
v_size_378_ = lean_ctor_get(v_t_376_, 0);
v_k_379_ = lean_ctor_get(v_t_376_, 1);
v_v_380_ = lean_ctor_get(v_t_376_, 2);
v_l_381_ = lean_ctor_get(v_t_376_, 3);
v_r_382_ = lean_ctor_get(v_t_376_, 4);
v_isSharedCheck_398_ = !lean_is_exclusive(v_t_376_);
if (v_isSharedCheck_398_ == 0)
{
v___x_384_ = v_t_376_;
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_r_382_);
lean_inc(v_l_381_);
lean_inc(v_v_380_);
lean_inc(v_k_379_);
lean_inc(v_size_378_);
lean_dec(v_t_376_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_lt(v_k_375_, v_k_379_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_eq(v_k_375_, v_k_379_);
if (v___x_387_ == 0)
{
lean_object* v_impl_388_; lean_object* v___x_389_; 
lean_del_object(v___x_384_);
lean_dec(v_size_378_);
v_impl_388_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_374_, v_k_375_, v_r_382_);
v___x_389_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_379_, v_v_380_, v_l_381_, v_impl_388_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_val_392_; lean_object* v___x_394_; 
lean_dec(v_k_379_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_v_380_);
v___x_391_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(v_b_u2082_374_, v___f_377_, v___x_390_);
v_val_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_392_);
lean_dec(v___x_391_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 2, v_val_392_);
lean_ctor_set(v___x_384_, 1, v_k_375_);
v___x_394_ = v___x_384_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_size_378_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_375_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_val_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_l_381_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_r_382_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_impl_396_; lean_object* v___x_397_; 
lean_del_object(v___x_384_);
lean_dec(v_size_378_);
v_impl_396_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_374_, v_k_375_, v_l_381_);
v___x_397_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_379_, v_v_380_, v_impl_396_, v_r_382_);
return v___x_397_;
}
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_val_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_399_ = lean_box(0);
v___x_400_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(v_b_u2082_374_, v___f_377_, v___x_399_);
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec(v___x_400_);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_k_375_);
lean_ctor_set(v___x_403_, 2, v_val_401_);
lean_ctor_set(v___x_403_, 3, v_t_376_);
lean_ctor_set(v___x_403_, 4, v_t_376_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(lean_object* v_init_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v_k_406_; lean_object* v_v_407_; lean_object* v_l_408_; lean_object* v_r_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_k_406_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_k_406_);
v_v_407_ = lean_ctor_get(v_x_405_, 2);
lean_inc(v_v_407_);
v_l_408_ = lean_ctor_get(v_x_405_, 3);
lean_inc(v_l_408_);
v_r_409_ = lean_ctor_get(v_x_405_, 4);
lean_inc(v_r_409_);
lean_dec_ref(v_x_405_);
v___x_410_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_init_404_, v_l_408_);
v___x_411_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_v_407_, v_k_406_, v___x_410_);
v_init_404_ = v___x_411_;
v_x_405_ = v_r_409_;
goto _start;
}
else
{
return v_init_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge(lean_object* v_t_u2081_413_, lean_object* v_t_u2082_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_t_u2081_413_, v_t_u2082_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0(lean_object* v_b_u2082_416_, lean_object* v_k_417_, lean_object* v_t_418_, lean_object* v_hl_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_416_, v_k_417_, v_t_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1(lean_object* v_init_421_, lean_object* v_t_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_init_421_, v_t_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0(lean_object* v_toPure_424_, lean_object* v_____do__lift_425_){
_start:
{
lean_object* v_expr_426_; lean_object* v___x_427_; 
v_expr_426_ = lean_ctor_get(v_____do__lift_425_, 0);
lean_inc_ref(v_expr_426_);
lean_dec_ref(v_____do__lift_425_);
v___x_427_ = lean_apply_2(v_toPure_424_, lean_box(0), v_expr_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(lean_object* v_inst_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v_toApplicative_430_; lean_object* v_toBind_431_; lean_object* v_toPure_432_; lean_object* v___f_433_; lean_object* v___x_434_; 
v_toApplicative_430_ = lean_ctor_get(v_inst_428_, 0);
lean_inc_ref(v_toApplicative_430_);
v_toBind_431_ = lean_ctor_get(v_inst_428_, 1);
lean_inc(v_toBind_431_);
lean_dec_ref(v_inst_428_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_430_, 1);
lean_inc(v_toPure_432_);
lean_dec_ref(v_toApplicative_430_);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_433_, 0, v_toPure_432_);
v___x_434_ = lean_apply_4(v_toBind_431_, lean_box(0), lean_box(0), v_inst_429_, v___f_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr(lean_object* v_m_435_, lean_object* v_inst_436_, lean_object* v_inst_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_436_, v_inst_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0(lean_object* v_toPure_439_, lean_object* v_____do__lift_440_){
_start:
{
lean_object* v_pos_441_; lean_object* v___x_442_; 
v_pos_441_ = lean_ctor_get(v_____do__lift_440_, 1);
lean_inc(v_pos_441_);
lean_dec_ref(v_____do__lift_440_);
v___x_442_ = lean_apply_2(v_toPure_439_, lean_box(0), v_pos_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v_toPure_447_; lean_object* v___f_448_; lean_object* v___x_449_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_443_, 0);
lean_inc_ref(v_toApplicative_445_);
v_toBind_446_ = lean_ctor_get(v_inst_443_, 1);
lean_inc(v_toBind_446_);
lean_dec_ref(v_inst_443_);
v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc(v_toPure_447_);
lean_dec_ref(v_toApplicative_445_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0), 2, 1);
lean_closure_set(v___f_448_, 0, v_toPure_447_);
v___x_449_ = lean_apply_4(v_toBind_446_, lean_box(0), lean_box(0), v_inst_444_, v___f_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos(lean_object* v_m_450_, lean_object* v_inst_451_, lean_object* v_inst_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_451_, v_inst_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0(lean_object* v_childIdx_454_, lean_object* v_child_455_, lean_object* v_cfg_456_){
_start:
{
lean_object* v_pos_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_pos_457_ = lean_ctor_get(v_cfg_456_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_cfg_456_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_cfg_456_, 0);
lean_dec(v_unused_466_);
v___x_459_ = v_cfg_456_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_pos_457_);
lean_dec(v_cfg_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = l_Lean_SubExpr_Pos_push(v_pos_457_, v_childIdx_454_);
lean_dec(v_pos_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_461_);
lean_ctor_set(v___x_459_, 0, v_child_455_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_child_455_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(lean_object* v_inst_467_, lean_object* v_child_468_, lean_object* v_childIdx_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___f_471_; lean_object* v___x_472_; 
v___f_471_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0), 3, 2);
lean_closure_set(v___f_471_, 0, v_childIdx_469_);
lean_closure_set(v___f_471_, 1, v_child_468_);
v___x_472_ = lean_apply_3(v_inst_467_, lean_box(0), v___f_471_, v_x_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend(lean_object* v_00_u03b1_473_, lean_object* v_m_474_, lean_object* v_inst_475_, lean_object* v_child_476_, lean_object* v_childIdx_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_475_, v_child_476_, v_childIdx_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(lean_object* v_inst_480_, lean_object* v_x_481_, lean_object* v_____do__lift_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_Expr_appFn_x21(v_____do__lift_482_);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_480_, v___x_483_, v___x_484_, v_x_481_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed(lean_object* v_inst_486_, lean_object* v_x_487_, lean_object* v_____do__lift_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(v_inst_486_, v_x_487_, v_____do__lift_488_);
lean_dec_ref(v_____do__lift_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_toBind_494_; lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_toBind_494_ = lean_ctor_get(v_inst_490_, 1);
lean_inc(v_toBind_494_);
v___f_495_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_495_, 0, v_inst_492_);
lean_closure_set(v___f_495_, 1, v_x_493_);
v___x_496_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_490_, v_inst_491_);
v___x_497_ = lean_apply_4(v_toBind_494_, lean_box(0), lean_box(0), v___x_496_, v___f_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn(lean_object* v_00_u03b1_498_, lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(lean_object* v_inst_505_, lean_object* v_x_506_, lean_object* v_____do__lift_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = l_Lean_Expr_appArg_x21(v_____do__lift_507_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_505_, v___x_508_, v___x_509_, v_x_506_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed(lean_object* v_inst_511_, lean_object* v_x_512_, lean_object* v_____do__lift_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(v_inst_511_, v_x_512_, v_____do__lift_513_);
lean_dec_ref(v_____do__lift_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_toBind_519_; lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_toBind_519_ = lean_ctor_get(v_inst_515_, 1);
lean_inc(v_toBind_519_);
v___f_520_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_520_, 0, v_inst_517_);
lean_closure_set(v___f_520_, 1, v_x_518_);
v___x_521_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_515_, v_inst_516_);
v___x_522_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v___x_521_, v___f_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg(lean_object* v_00_u03b1_523_, lean_object* v_m_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(v_inst_525_, v_inst_526_, v_inst_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0(lean_object* v_inst_530_, lean_object* v_x_531_, lean_object* v_____do__lift_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_534_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_530_, v_____do__lift_532_, v___x_533_, v_x_531_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__1(lean_object* v_inst_535_, lean_object* v_toBind_536_, lean_object* v___f_537_, lean_object* v_____do__lift_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_539_, 0, v_____do__lift_538_);
v___x_540_ = lean_apply_2(v_inst_535_, lean_box(0), v___x_539_);
v___x_541_ = lean_apply_4(v_toBind_536_, lean_box(0), lean_box(0), v___x_540_, v___f_537_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_toBind_547_; lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_toBind_547_ = lean_ctor_get(v_inst_542_, 1);
lean_inc_n(v_toBind_547_, 2);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0), 3, 2);
lean_closure_set(v___f_548_, 0, v_inst_544_);
lean_closure_set(v___f_548_, 1, v_x_546_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__1), 4, 3);
lean_closure_set(v___f_549_, 0, v_inst_545_);
lean_closure_set(v___f_549_, 1, v_toBind_547_);
lean_closure_set(v___f_549_, 2, v___f_548_);
v___x_550_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_542_, v_inst_543_);
v___x_551_ = lean_apply_4(v_toBind_547_, lean_box(0), lean_box(0), v___x_550_, v___f_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType(lean_object* v_00_u03b1_552_, lean_object* v_m_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg(v_inst_554_, v_inst_555_, v_inst_556_, v_inst_557_, v_x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__0(lean_object* v_xa_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_acc_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_apply_1(v_xa_560_, v_acc_564_);
v___x_566_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(v_inst_561_, v_inst_562_, v_inst_563_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1(lean_object* v_xf_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_xa_571_, lean_object* v_toBind_572_, lean_object* v___f_573_, lean_object* v_____do__lift_574_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = l_Lean_Expr_isApp(v_____do__lift_574_);
if (v___x_575_ == 0)
{
lean_dec(v___f_573_);
lean_dec(v_toBind_572_);
lean_dec(v_xa_571_);
lean_dec(v_inst_570_);
lean_dec(v_inst_569_);
lean_dec_ref(v_inst_568_);
return v_xf_567_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_inc(v_inst_570_);
lean_inc(v_inst_569_);
lean_inc_ref(v_inst_568_);
v___x_576_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(v_inst_568_, v_inst_569_, v_inst_570_, v_xf_567_, v_xa_571_);
v___x_577_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(v_inst_568_, v_inst_569_, v_inst_570_, v___x_576_);
v___x_578_ = lean_apply_4(v_toBind_572_, lean_box(0), lean_box(0), v___x_577_, v___f_573_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed(lean_object* v_xf_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_xa_583_, lean_object* v_toBind_584_, lean_object* v___f_585_, lean_object* v_____do__lift_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1(v_xf_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_xa_583_, v_toBind_584_, v___f_585_, v_____do__lift_586_);
lean_dec_ref(v_____do__lift_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_xf_591_, lean_object* v_xa_592_){
_start:
{
lean_object* v_toBind_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_toBind_593_ = lean_ctor_get(v_inst_588_, 1);
lean_inc_n(v_toBind_593_, 2);
lean_inc(v_inst_590_);
lean_inc_n(v_inst_589_, 2);
lean_inc_ref_n(v_inst_588_, 2);
lean_inc(v_xa_592_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__0), 5, 4);
lean_closure_set(v___f_594_, 0, v_xa_592_);
lean_closure_set(v___f_594_, 1, v_inst_588_);
lean_closure_set(v___f_594_, 2, v_inst_589_);
lean_closure_set(v___f_594_, 3, v_inst_590_);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_595_, 0, v_xf_591_);
lean_closure_set(v___f_595_, 1, v_inst_588_);
lean_closure_set(v___f_595_, 2, v_inst_589_);
lean_closure_set(v___f_595_, 3, v_inst_590_);
lean_closure_set(v___f_595_, 4, v_xa_592_);
lean_closure_set(v___f_595_, 5, v_toBind_593_);
lean_closure_set(v___f_595_, 6, v___f_594_);
v___x_596_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_588_, v_inst_589_);
v___x_597_ = lean_apply_4(v_toBind_593_, lean_box(0), lean_box(0), v___x_596_, v___f_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs(lean_object* v_00_u03b1_598_, lean_object* v_m_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_xf_603_, lean_object* v_xa_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(v_inst_600_, v_inst_601_, v_inst_602_, v_xf_603_, v_xa_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__0(lean_object* v_xa_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_acc_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_apply_1(v_xa_606_, v_acc_610_);
v___x_612_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(v_inst_607_, v_inst_608_, v_inst_609_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1(lean_object* v_maxArgs_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_xf_617_, lean_object* v_xa_618_, lean_object* v_toBind_619_, lean_object* v___f_620_, lean_object* v_____do__lift_621_){
_start:
{
lean_object* v_zero_622_; uint8_t v_isZero_623_; 
v_zero_622_ = lean_unsigned_to_nat(0u);
v_isZero_623_ = lean_nat_dec_eq(v_maxArgs_613_, v_zero_622_);
if (v_isZero_623_ == 0)
{
if (lean_obj_tag(v_____do__lift_621_) == 5)
{
lean_object* v_one_624_; lean_object* v_n_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_one_624_ = lean_unsigned_to_nat(1u);
v_n_625_ = lean_nat_sub(v_maxArgs_613_, v_one_624_);
lean_inc(v_inst_616_);
lean_inc(v_inst_615_);
lean_inc_ref(v_inst_614_);
v___x_626_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(v_inst_614_, v_inst_615_, v_inst_616_, v_n_625_, v_xf_617_, v_xa_618_);
v___x_627_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(v_inst_614_, v_inst_615_, v_inst_616_, v___x_626_);
v___x_628_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v___x_627_, v___f_620_);
return v___x_628_;
}
else
{
lean_dec(v___f_620_);
lean_dec(v_toBind_619_);
lean_dec(v_xa_618_);
lean_dec(v_inst_616_);
lean_dec(v_inst_615_);
lean_dec_ref(v_inst_614_);
return v_xf_617_;
}
}
else
{
lean_dec(v___f_620_);
lean_dec(v_toBind_619_);
lean_dec(v_xa_618_);
lean_dec(v_inst_616_);
lean_dec(v_inst_615_);
lean_dec_ref(v_inst_614_);
return v_xf_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed(lean_object* v_maxArgs_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_xf_633_, lean_object* v_xa_634_, lean_object* v_toBind_635_, lean_object* v___f_636_, lean_object* v_____do__lift_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1(v_maxArgs_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_xf_633_, v_xa_634_, v_toBind_635_, v___f_636_, v_____do__lift_637_);
lean_dec_ref(v_____do__lift_637_);
lean_dec(v_maxArgs_629_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_maxArgs_642_, lean_object* v_xf_643_, lean_object* v_xa_644_){
_start:
{
lean_object* v_toBind_645_; lean_object* v___f_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_toBind_645_ = lean_ctor_get(v_inst_639_, 1);
lean_inc_n(v_toBind_645_, 2);
lean_inc(v_inst_641_);
lean_inc_n(v_inst_640_, 2);
lean_inc_ref_n(v_inst_639_, 2);
lean_inc(v_xa_644_);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__0), 5, 4);
lean_closure_set(v___f_646_, 0, v_xa_644_);
lean_closure_set(v___f_646_, 1, v_inst_639_);
lean_closure_set(v___f_646_, 2, v_inst_640_);
lean_closure_set(v___f_646_, 3, v_inst_641_);
v___f_647_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_647_, 0, v_maxArgs_642_);
lean_closure_set(v___f_647_, 1, v_inst_639_);
lean_closure_set(v___f_647_, 2, v_inst_640_);
lean_closure_set(v___f_647_, 3, v_inst_641_);
lean_closure_set(v___f_647_, 4, v_xf_643_);
lean_closure_set(v___f_647_, 5, v_xa_644_);
lean_closure_set(v___f_647_, 6, v_toBind_645_);
lean_closure_set(v___f_647_, 7, v___f_646_);
v___x_648_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_639_, v_inst_640_);
v___x_649_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v___x_648_, v___f_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs(lean_object* v_00_u03b1_650_, lean_object* v_m_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_maxArgs_655_, lean_object* v_xf_656_, lean_object* v_xa_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(v_inst_652_, v_inst_653_, v_inst_654_, v_maxArgs_655_, v_xf_656_, v_xa_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0(lean_object* v___y_659_, lean_object* v_e_660_, lean_object* v_newPos_661_, lean_object* v_cfg_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = l_Lean_Expr_getBoundedAppFn(v___y_659_, v_e_660_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_newPos_661_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed(lean_object* v___y_665_, lean_object* v_e_666_, lean_object* v_newPos_667_, lean_object* v_cfg_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0(v___y_665_, v_e_666_, v_newPos_667_, v_cfg_668_);
lean_dec_ref(v_cfg_668_);
lean_dec_ref(v_e_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(lean_object* v___y_670_, lean_object* v_e_671_, lean_object* v_inst_672_, lean_object* v_xf_673_, lean_object* v_____do__lift_674_){
_start:
{
lean_object* v_newPos_675_; lean_object* v___f_676_; lean_object* v___x_677_; 
v_newPos_675_ = l_Lean_SubExpr_Pos_pushNaryFn(v___y_670_, v_____do__lift_674_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_676_, 0, v___y_670_);
lean_closure_set(v___f_676_, 1, v_e_671_);
lean_closure_set(v___f_676_, 2, v_newPos_675_);
v___x_677_ = lean_apply_3(v_inst_672_, lean_box(0), v___f_676_, v_xf_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed(lean_object* v___y_678_, lean_object* v_e_679_, lean_object* v_inst_680_, lean_object* v_xf_681_, lean_object* v_____do__lift_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(v___y_678_, v_e_679_, v_inst_680_, v_xf_681_, v_____do__lift_682_);
lean_dec(v_____do__lift_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2(lean_object* v_inst_684_, lean_object* v_xf_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_toBind_688_, lean_object* v_maxArgs_689_, lean_object* v_e_690_){
_start:
{
lean_object* v___y_692_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = l_Lean_Expr_getAppNumArgs(v_e_690_);
v___x_697_ = lean_nat_dec_le(v_maxArgs_689_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec(v_maxArgs_689_);
v___y_692_ = v___x_696_;
goto v___jp_691_;
}
else
{
lean_dec(v___x_696_);
v___y_692_ = v_maxArgs_689_;
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___f_693_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_693_, 0, v___y_692_);
lean_closure_set(v___f_693_, 1, v_e_690_);
lean_closure_set(v___f_693_, 2, v_inst_684_);
lean_closure_set(v___f_693_, 3, v_xf_685_);
v___x_694_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_686_, v_inst_687_);
v___x_695_ = lean_apply_4(v_toBind_688_, lean_box(0), lean_box(0), v___x_694_, v___f_693_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg(lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_maxArgs_701_, lean_object* v_xf_702_){
_start:
{
lean_object* v_toBind_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_toBind_703_ = lean_ctor_get(v_inst_698_, 1);
lean_inc_n(v_toBind_703_, 2);
lean_inc(v_inst_699_);
lean_inc_ref(v_inst_698_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2), 7, 6);
lean_closure_set(v___f_704_, 0, v_inst_700_);
lean_closure_set(v___f_704_, 1, v_xf_702_);
lean_closure_set(v___f_704_, 2, v_inst_698_);
lean_closure_set(v___f_704_, 3, v_inst_699_);
lean_closure_set(v___f_704_, 4, v_toBind_703_);
lean_closure_set(v___f_704_, 5, v_maxArgs_701_);
v___x_705_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_698_, v_inst_699_);
v___x_706_ = lean_apply_4(v_toBind_703_, lean_box(0), lean_box(0), v___x_705_, v___f_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn(lean_object* v_00_u03b1_707_, lean_object* v_m_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_maxArgs_712_, lean_object* v_xf_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg(v_inst_709_, v_inst_710_, v_inst_711_, v_maxArgs_712_, v_xf_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0(lean_object* v_inst_715_, lean_object* v_x_716_, lean_object* v_____do__lift_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_Expr_bindingDomain_x21(v_____do__lift_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_715_, v___x_718_, v___x_719_, v_x_716_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed(lean_object* v_inst_721_, lean_object* v_x_722_, lean_object* v_____do__lift_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0(v_inst_721_, v_x_722_, v_____do__lift_723_);
lean_dec_ref(v_____do__lift_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_x_728_){
_start:
{
lean_object* v_toBind_729_; lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_toBind_729_ = lean_ctor_get(v_inst_725_, 1);
lean_inc(v_toBind_729_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_730_, 0, v_inst_727_);
lean_closure_set(v___f_730_, 1, v_x_728_);
v___x_731_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_725_, v_inst_726_);
v___x_732_ = lean_apply_4(v_toBind_729_, lean_box(0), lean_box(0), v___x_731_, v___f_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain(lean_object* v_00_u03b1_733_, lean_object* v_m_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(v_inst_735_, v_inst_736_, v_inst_737_, v_x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(lean_object* v_e_740_, lean_object* v_fvar_741_, lean_object* v_x_742_, lean_object* v_inst_743_, lean_object* v_b_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_745_ = l_Lean_Expr_bindingBody_x21(v_e_740_);
v___x_746_ = lean_expr_instantiate1(v___x_745_, v_fvar_741_);
lean_dec_ref(v___x_745_);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_apply_1(v_x_742_, v_b_744_);
v___x_749_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_743_, v___x_746_, v___x_747_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed(lean_object* v_e_750_, lean_object* v_fvar_751_, lean_object* v_x_752_, lean_object* v_inst_753_, lean_object* v_b_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(v_e_750_, v_fvar_751_, v_x_752_, v_inst_753_, v_b_754_);
lean_dec_ref(v_fvar_751_);
lean_dec_ref(v_e_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1(lean_object* v_e_756_, lean_object* v_x_757_, lean_object* v_inst_758_, lean_object* v_v_759_, lean_object* v_toBind_760_, lean_object* v_fvar_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_inc_ref(v_fvar_761_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_762_, 0, v_e_756_);
lean_closure_set(v___f_762_, 1, v_fvar_761_);
lean_closure_set(v___f_762_, 2, v_x_757_);
lean_closure_set(v___f_762_, 3, v_inst_758_);
v___x_763_ = lean_apply_1(v_v_759_, v_fvar_761_);
v___x_764_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_763_, v___f_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2(lean_object* v_x_765_, lean_object* v_inst_766_, lean_object* v_v_767_, lean_object* v_toBind_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_n_771_, lean_object* v_e_772_){
_start:
{
lean_object* v___f_773_; uint8_t v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; 
lean_inc_ref(v_e_772_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_773_, 0, v_e_772_);
lean_closure_set(v___f_773_, 1, v_x_765_);
lean_closure_set(v___f_773_, 2, v_inst_766_);
lean_closure_set(v___f_773_, 3, v_v_767_);
lean_closure_set(v___f_773_, 4, v_toBind_768_);
v___x_774_ = l_Lean_Expr_binderInfo(v_e_772_);
v___x_775_ = l_Lean_Expr_bindingDomain_x21(v_e_772_);
lean_dec_ref(v_e_772_);
v___x_776_ = 0;
v___x_777_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_769_, v_inst_770_, v_n_771_, v___x_774_, v___x_775_, v___f_773_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_n_782_, lean_object* v_v_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_toBind_785_; lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_toBind_785_ = lean_ctor_get(v_inst_778_, 1);
lean_inc_n(v_toBind_785_, 2);
lean_inc_ref(v_inst_778_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2), 8, 7);
lean_closure_set(v___f_786_, 0, v_x_784_);
lean_closure_set(v___f_786_, 1, v_inst_780_);
lean_closure_set(v___f_786_, 2, v_v_783_);
lean_closure_set(v___f_786_, 3, v_toBind_785_);
lean_closure_set(v___f_786_, 4, v_inst_781_);
lean_closure_set(v___f_786_, 5, v_inst_778_);
lean_closure_set(v___f_786_, 6, v_n_782_);
v___x_787_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_778_, v_inst_779_);
v___x_788_ = lean_apply_4(v_toBind_785_, lean_box(0), lean_box(0), v___x_787_, v___f_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27(lean_object* v_00_u03b1_789_, lean_object* v_m_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_00_u03b2_795_, lean_object* v_n_796_, lean_object* v_v_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(v_inst_791_, v_inst_792_, v_inst_793_, v_inst_794_, v_n_796_, v_v_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_inc(v_x_800_);
return v_x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed(lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0(v_x_802_, v_x_803_);
lean_dec(v_x_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(lean_object* v_toPure_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_box(0);
v___x_808_ = lean_apply_2(v_toPure_805_, lean_box(0), v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed(lean_object* v_toPure_809_, lean_object* v_x_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(v_toPure_809_, v_x_810_);
lean_dec_ref(v_x_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_n_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_toApplicative_818_; lean_object* v_toPure_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___x_822_; 
v_toApplicative_818_ = lean_ctor_get(v_inst_812_, 0);
v_toPure_819_ = lean_ctor_get(v_toApplicative_818_, 1);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_820_, 0, v_x_817_);
lean_inc(v_toPure_819_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_821_, 0, v_toPure_819_);
v___x_822_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(v_inst_812_, v_inst_813_, v_inst_814_, v_inst_815_, v_n_816_, v___f_821_, v___f_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody(lean_object* v_00_u03b1_823_, lean_object* v_m_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_n_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg(v_inst_825_, v_inst_826_, v_inst_827_, v_inst_828_, v_n_829_, v_x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_835_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2));
v___x_836_ = lean_unsigned_to_nat(34u);
v___x_837_ = lean_unsigned_to_nat(110u);
v___x_838_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1));
v___x_839_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0));
v___x_840_ = l_mkPanicMessageWithDecl(v___x_839_, v___x_838_, v___x_837_, v___x_836_, v___x_835_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0(lean_object* v_inst_841_, lean_object* v_x_842_, lean_object* v___x_843_, lean_object* v_____x_844_){
_start:
{
if (lean_obj_tag(v_____x_844_) == 11)
{
lean_object* v_struct_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_struct_845_ = lean_ctor_get(v_____x_844_, 2);
lean_inc_ref(v_struct_845_);
lean_dec_ref(v_____x_844_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_841_, v_struct_845_, v___x_846_, v_x_842_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_____x_844_);
lean_dec(v_x_842_);
lean_dec(v_inst_841_);
v___x_848_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3);
v___x_849_ = l_panic___redArg(v___x_843_, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed(lean_object* v_inst_850_, lean_object* v_x_851_, lean_object* v___x_852_, lean_object* v_____x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0(v_inst_850_, v_x_851_, v___x_852_, v_____x_853_);
lean_dec(v___x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg(lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_toBind_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___x_864_; 
v_toBind_860_ = lean_ctor_get(v_inst_856_, 1);
lean_inc(v_toBind_860_);
lean_inc_ref(v_inst_856_);
v___x_861_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_856_, v_inst_857_);
v___x_862_ = l_instInhabitedOfMonad___redArg(v_inst_856_, v_inst_855_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_863_, 0, v_inst_858_);
lean_closure_set(v___f_863_, 1, v_x_859_);
lean_closure_set(v___f_863_, 2, v___x_862_);
v___x_864_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_861_, v___f_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj(lean_object* v_00_u03b1_865_, lean_object* v_inst_866_, lean_object* v_m_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg(v_inst_866_, v_inst_868_, v_inst_869_, v_inst_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__0(lean_object* v_expr_873_, lean_object* v_ctx_874_){
_start:
{
lean_object* v_pos_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_pos_875_ = lean_ctor_get(v_ctx_874_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_ctx_874_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_ctx_874_, 0);
lean_dec(v_unused_883_);
v___x_877_ = v_ctx_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_pos_875_);
lean_dec(v_ctx_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v_expr_873_);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_expr_873_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_pos_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_885_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2));
v___x_886_ = lean_unsigned_to_nat(33u);
v___x_887_ = lean_unsigned_to_nat(114u);
v___x_888_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0));
v___x_889_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0));
v___x_890_ = l_mkPanicMessageWithDecl(v___x_889_, v___x_888_, v___x_887_, v___x_886_, v___x_885_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1(lean_object* v_inst_891_, lean_object* v_x_892_, lean_object* v___x_893_, lean_object* v_____x_894_){
_start:
{
if (lean_obj_tag(v_____x_894_) == 10)
{
lean_object* v_expr_895_; lean_object* v___f_896_; lean_object* v___x_897_; 
v_expr_895_ = lean_ctor_get(v_____x_894_, 1);
lean_inc_ref(v_expr_895_);
lean_dec_ref(v_____x_894_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_896_, 0, v_expr_895_);
v___x_897_ = lean_apply_3(v_inst_891_, lean_box(0), v___f_896_, v_x_892_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v_____x_894_);
lean_dec(v_x_892_);
lean_dec(v_inst_891_);
v___x_898_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1);
v___x_899_ = l_panic___redArg(v___x_893_, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed(lean_object* v_inst_900_, lean_object* v_x_901_, lean_object* v___x_902_, lean_object* v_____x_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1(v_inst_900_, v_x_901_, v___x_902_, v_____x_903_);
lean_dec(v___x_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg(lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_x_909_){
_start:
{
lean_object* v_toBind_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; 
v_toBind_910_ = lean_ctor_get(v_inst_906_, 1);
lean_inc(v_toBind_910_);
lean_inc_ref(v_inst_906_);
v___x_911_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_906_, v_inst_907_);
v___x_912_ = l_instInhabitedOfMonad___redArg(v_inst_906_, v_inst_905_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_913_, 0, v_inst_908_);
lean_closure_set(v___f_913_, 1, v_x_909_);
lean_closure_set(v___f_913_, 2, v___x_912_);
v___x_914_ = lean_apply_4(v_toBind_910_, lean_box(0), lean_box(0), v___x_911_, v___f_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr(lean_object* v_00_u03b1_915_, lean_object* v_inst_916_, lean_object* v_m_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg(v_inst_916_, v_inst_918_, v_inst_919_, v_inst_920_, v_x_921_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_924_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2));
v___x_925_ = lean_unsigned_to_nat(38u);
v___x_926_ = lean_unsigned_to_nat(118u);
v___x_927_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0));
v___x_928_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0));
v___x_929_ = l_mkPanicMessageWithDecl(v___x_928_, v___x_927_, v___x_926_, v___x_925_, v___x_924_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0(lean_object* v_inst_930_, lean_object* v_x_931_, lean_object* v___x_932_, lean_object* v_____x_933_){
_start:
{
if (lean_obj_tag(v_____x_933_) == 8)
{
lean_object* v_type_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_type_934_ = lean_ctor_get(v_____x_933_, 1);
lean_inc_ref(v_type_934_);
lean_dec_ref(v_____x_933_);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_930_, v_type_934_, v___x_935_, v_x_931_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_____x_933_);
lean_dec(v_x_931_);
lean_dec(v_inst_930_);
v___x_937_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1);
v___x_938_ = l_panic___redArg(v___x_932_, v___x_937_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed(lean_object* v_inst_939_, lean_object* v_x_940_, lean_object* v___x_941_, lean_object* v_____x_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0(v_inst_939_, v_x_940_, v___x_941_, v_____x_942_);
lean_dec(v___x_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg(lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_x_948_){
_start:
{
lean_object* v_toBind_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___f_952_; lean_object* v___x_953_; 
v_toBind_949_ = lean_ctor_get(v_inst_945_, 1);
lean_inc(v_toBind_949_);
lean_inc_ref(v_inst_945_);
v___x_950_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_945_, v_inst_946_);
v___x_951_ = l_instInhabitedOfMonad___redArg(v_inst_945_, v_inst_944_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_952_, 0, v_inst_947_);
lean_closure_set(v___f_952_, 1, v_x_948_);
lean_closure_set(v___f_952_, 2, v___x_951_);
v___x_953_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___x_950_, v___f_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType(lean_object* v_00_u03b1_954_, lean_object* v_inst_955_, lean_object* v_m_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg(v_inst_955_, v_inst_957_, v_inst_958_, v_inst_959_, v_x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_963_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2));
v___x_964_ = lean_unsigned_to_nat(38u);
v___x_965_ = lean_unsigned_to_nat(122u);
v___x_966_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0));
v___x_967_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0));
v___x_968_ = l_mkPanicMessageWithDecl(v___x_967_, v___x_966_, v___x_965_, v___x_964_, v___x_963_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0(lean_object* v_inst_969_, lean_object* v_x_970_, lean_object* v___x_971_, lean_object* v_____x_972_){
_start:
{
if (lean_obj_tag(v_____x_972_) == 8)
{
lean_object* v_value_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_value_973_ = lean_ctor_get(v_____x_972_, 2);
lean_inc_ref(v_value_973_);
lean_dec_ref(v_____x_972_);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_969_, v_value_973_, v___x_974_, v_x_970_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec_ref(v_____x_972_);
lean_dec(v_x_970_);
lean_dec(v_inst_969_);
v___x_976_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1);
v___x_977_ = l_panic___redArg(v___x_971_, v___x_976_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed(lean_object* v_inst_978_, lean_object* v_x_979_, lean_object* v___x_980_, lean_object* v_____x_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0(v_inst_978_, v_x_979_, v___x_980_, v_____x_981_);
lean_dec(v___x_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg(lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_toBind_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___f_991_; lean_object* v___x_992_; 
v_toBind_988_ = lean_ctor_get(v_inst_984_, 1);
lean_inc(v_toBind_988_);
lean_inc_ref(v_inst_984_);
v___x_989_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_984_, v_inst_985_);
v___x_990_ = l_instInhabitedOfMonad___redArg(v_inst_984_, v_inst_983_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_991_, 0, v_inst_986_);
lean_closure_set(v___f_991_, 1, v_x_987_);
lean_closure_set(v___f_991_, 2, v___x_990_);
v___x_992_ = lean_apply_4(v_toBind_988_, lean_box(0), lean_box(0), v___x_989_, v___f_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue(lean_object* v_00_u03b1_993_, lean_object* v_inst_994_, lean_object* v_m_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_x_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg(v_inst_994_, v_inst_996_, v_inst_997_, v_inst_998_, v_x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0(lean_object* v_body_1001_, lean_object* v_inst_1002_, lean_object* v_x_1003_, lean_object* v_fvar_1004_){
_start:
{
lean_object* v_b_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_b_1005_ = lean_expr_instantiate1(v_body_1001_, v_fvar_1004_);
v___x_1006_ = lean_unsigned_to_nat(2u);
v___x_1007_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(v_inst_1002_, v_b_1005_, v___x_1006_, v_x_1003_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed(lean_object* v_body_1008_, lean_object* v_inst_1009_, lean_object* v_x_1010_, lean_object* v_fvar_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0(v_body_1008_, v_inst_1009_, v_x_1010_, v_fvar_1011_);
lean_dec_ref(v_fvar_1011_);
lean_dec_ref(v_body_1008_);
return v_res_1012_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1014_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2));
v___x_1015_ = lean_unsigned_to_nat(43u);
v___x_1016_ = lean_unsigned_to_nat(126u);
v___x_1017_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0));
v___x_1018_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0));
v___x_1019_ = l_mkPanicMessageWithDecl(v___x_1018_, v___x_1017_, v___x_1016_, v___x_1015_, v___x_1014_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1(lean_object* v_inst_1020_, lean_object* v_x_1021_, lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v___x_1024_, lean_object* v_____x_1025_){
_start:
{
if (lean_obj_tag(v_____x_1025_) == 8)
{
lean_object* v_declName_1026_; lean_object* v_type_1027_; lean_object* v_value_1028_; lean_object* v_body_1029_; uint8_t v_nondep_1030_; lean_object* v___f_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; 
v_declName_1026_ = lean_ctor_get(v_____x_1025_, 0);
lean_inc(v_declName_1026_);
v_type_1027_ = lean_ctor_get(v_____x_1025_, 1);
lean_inc_ref(v_type_1027_);
v_value_1028_ = lean_ctor_get(v_____x_1025_, 2);
lean_inc_ref(v_value_1028_);
v_body_1029_ = lean_ctor_get(v_____x_1025_, 3);
lean_inc_ref(v_body_1029_);
v_nondep_1030_ = lean_ctor_get_uint8(v_____x_1025_, sizeof(void*)*4 + 8);
lean_dec_ref(v_____x_1025_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1031_, 0, v_body_1029_);
lean_closure_set(v___f_1031_, 1, v_inst_1020_);
lean_closure_set(v___f_1031_, 2, v_x_1021_);
v___x_1032_ = 0;
v___x_1033_ = l_Lean_Meta_withLetDecl___redArg(v_inst_1022_, v_inst_1023_, v_declName_1026_, v_type_1027_, v_value_1028_, v___f_1031_, v_nondep_1030_, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref(v_____x_1025_);
lean_dec_ref(v_inst_1023_);
lean_dec_ref(v_inst_1022_);
lean_dec(v_x_1021_);
lean_dec(v_inst_1020_);
v___x_1034_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1);
v___x_1035_ = l_panic___redArg(v___x_1024_, v___x_1034_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed(lean_object* v_inst_1036_, lean_object* v_x_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v___x_1040_, lean_object* v_____x_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1(v_inst_1036_, v_x_1037_, v_inst_1038_, v_inst_1039_, v___x_1040_, v_____x_1041_);
lean_dec(v___x_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v_toBind_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; 
v_toBind_1049_ = lean_ctor_get(v_inst_1044_, 1);
lean_inc(v_toBind_1049_);
lean_inc_ref_n(v_inst_1044_, 2);
v___x_1050_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1044_, v_inst_1045_);
v___x_1051_ = l_instInhabitedOfMonad___redArg(v_inst_1044_, v_inst_1043_);
v___f_1052_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1052_, 0, v_inst_1046_);
lean_closure_set(v___f_1052_, 1, v_x_1048_);
lean_closure_set(v___f_1052_, 2, v_inst_1047_);
lean_closure_set(v___f_1052_, 3, v_inst_1044_);
lean_closure_set(v___f_1052_, 4, v___x_1051_);
v___x_1053_ = lean_apply_4(v_toBind_1049_, lean_box(0), lean_box(0), v___x_1050_, v___f_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody(lean_object* v_00_u03b1_1054_, lean_object* v_inst_1055_, lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg(v_inst_1055_, v_inst_1057_, v_inst_1058_, v_inst_1059_, v_inst_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0(lean_object* v_e_1063_, lean_object* v_newPos_1064_, lean_object* v_cfg_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Lean_Expr_getAppFn(v_e_1063_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_newPos_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed(lean_object* v_e_1068_, lean_object* v_newPos_1069_, lean_object* v_cfg_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0(v_e_1068_, v_newPos_1069_, v_cfg_1070_);
lean_dec_ref(v_cfg_1070_);
lean_dec_ref(v_e_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(lean_object* v_e_1072_, lean_object* v_inst_1073_, lean_object* v_x_1074_, lean_object* v_____do__lift_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v_newPos_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; 
v___x_1076_ = l_Lean_Expr_getAppNumArgs(v_e_1072_);
v_newPos_1077_ = l_Lean_SubExpr_Pos_pushNaryFn(v___x_1076_, v_____do__lift_1075_);
lean_dec(v___x_1076_);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1078_, 0, v_e_1072_);
lean_closure_set(v___f_1078_, 1, v_newPos_1077_);
v___x_1079_ = lean_apply_3(v_inst_1073_, lean_box(0), v___f_1078_, v_x_1074_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed(lean_object* v_e_1080_, lean_object* v_inst_1081_, lean_object* v_x_1082_, lean_object* v_____do__lift_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(v_e_1080_, v_inst_1081_, v_x_1082_, v_____do__lift_1083_);
lean_dec(v_____do__lift_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2(lean_object* v_inst_1085_, lean_object* v_x_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_toBind_1089_, lean_object* v_e_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1091_, 0, v_e_1090_);
lean_closure_set(v___f_1091_, 1, v_inst_1085_);
lean_closure_set(v___f_1091_, 2, v_x_1086_);
v___x_1092_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_1087_, v_inst_1088_);
v___x_1093_ = lean_apply_4(v_toBind_1089_, lean_box(0), lean_box(0), v___x_1092_, v___f_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v_toBind_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_toBind_1098_ = lean_ctor_get(v_inst_1094_, 1);
lean_inc_n(v_toBind_1098_, 2);
lean_inc(v_inst_1095_);
lean_inc_ref(v_inst_1094_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1099_, 0, v_inst_1096_);
lean_closure_set(v___f_1099_, 1, v_x_1097_);
lean_closure_set(v___f_1099_, 2, v_inst_1094_);
lean_closure_set(v___f_1099_, 3, v_inst_1095_);
lean_closure_set(v___f_1099_, 4, v_toBind_1098_);
v___x_1100_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1094_, v_inst_1095_);
v___x_1101_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1100_, v___f_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn(lean_object* v_00_u03b1_1102_, lean_object* v_m_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(v_inst_1104_, v_inst_1105_, v_inst_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(lean_object* v___x_1109_, lean_object* v_args_1110_, lean_object* v_argIdx_1111_, lean_object* v_newPos_1112_, lean_object* v_cfg_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_array_get_borrowed(v___x_1109_, v_args_1110_, v_argIdx_1111_);
lean_inc(v___x_1114_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v_newPos_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed(lean_object* v___x_1116_, lean_object* v_args_1117_, lean_object* v_argIdx_1118_, lean_object* v_newPos_1119_, lean_object* v_cfg_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(v___x_1116_, v_args_1117_, v_argIdx_1118_, v_newPos_1119_, v_cfg_1120_);
lean_dec_ref(v_cfg_1120_);
lean_dec(v_argIdx_1118_);
lean_dec_ref(v_args_1117_);
lean_dec_ref(v___x_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(lean_object* v_args_1122_, lean_object* v_argIdx_1123_, lean_object* v___x_1124_, lean_object* v_inst_1125_, lean_object* v_x_1126_, lean_object* v_____do__lift_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v_newPos_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_array_get_size(v_args_1122_);
v_newPos_1129_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_1128_, v_argIdx_1123_, v_____do__lift_1127_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1130_, 0, v___x_1124_);
lean_closure_set(v___f_1130_, 1, v_args_1122_);
lean_closure_set(v___f_1130_, 2, v_argIdx_1123_);
lean_closure_set(v___f_1130_, 3, v_newPos_1129_);
v___x_1131_ = lean_apply_3(v_inst_1125_, lean_box(0), v___f_1130_, v_x_1126_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed(lean_object* v_args_1132_, lean_object* v_argIdx_1133_, lean_object* v___x_1134_, lean_object* v_inst_1135_, lean_object* v_x_1136_, lean_object* v_____do__lift_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(v_args_1132_, v_argIdx_1133_, v___x_1134_, v_inst_1135_, v_x_1136_, v_____do__lift_1137_);
lean_dec(v_____do__lift_1137_);
return v_res_1138_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1139_; lean_object* v_dummy_1140_; 
v___x_1139_ = lean_box(0);
v_dummy_1140_ = l_Lean_Expr_sort___override(v___x_1139_);
return v_dummy_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2(lean_object* v_argIdx_1141_, lean_object* v___x_1142_, lean_object* v_inst_1143_, lean_object* v_x_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_toBind_1147_, lean_object* v_e_1148_){
_start:
{
lean_object* v_dummy_1149_; lean_object* v_nargs_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_args_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_dummy_1149_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0);
v_nargs_1150_ = l_Lean_Expr_getAppNumArgs(v_e_1148_);
lean_inc(v_nargs_1150_);
v___x_1151_ = lean_mk_array(v_nargs_1150_, v_dummy_1149_);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_sub(v_nargs_1150_, v___x_1152_);
lean_dec(v_nargs_1150_);
v_args_1154_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1148_, v___x_1151_, v___x_1153_);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1155_, 0, v_args_1154_);
lean_closure_set(v___f_1155_, 1, v_argIdx_1141_);
lean_closure_set(v___f_1155_, 2, v___x_1142_);
lean_closure_set(v___f_1155_, 3, v_inst_1143_);
lean_closure_set(v___f_1155_, 4, v_x_1144_);
v___x_1156_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_1145_, v_inst_1146_);
v___x_1157_ = lean_apply_4(v_toBind_1147_, lean_box(0), lean_box(0), v___x_1156_, v___f_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg(lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_argIdx_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_toBind_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_toBind_1163_ = lean_ctor_get(v_inst_1158_, 1);
lean_inc_n(v_toBind_1163_, 2);
v___x_1164_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_1159_);
lean_inc_ref(v_inst_1158_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1165_, 0, v_argIdx_1161_);
lean_closure_set(v___f_1165_, 1, v___x_1164_);
lean_closure_set(v___f_1165_, 2, v_inst_1160_);
lean_closure_set(v___f_1165_, 3, v_x_1162_);
lean_closure_set(v___f_1165_, 4, v_inst_1158_);
lean_closure_set(v___f_1165_, 5, v_inst_1159_);
lean_closure_set(v___f_1165_, 6, v_toBind_1163_);
v___x_1166_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1158_, v_inst_1159_);
v___x_1167_ = lean_apply_4(v_toBind_1163_, lean_box(0), lean_box(0), v___x_1166_, v___f_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg(lean_object* v_00_u03b1_1168_, lean_object* v_m_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_argIdx_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg(v_inst_1170_, v_inst_1171_, v_inst_1172_, v_argIdx_1173_, v_x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_1177_ = lean_unsigned_to_nat(2u);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1176_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default(void){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0, &l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator(void){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default;
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(lean_object* v_iter_1181_){
_start:
{
lean_object* v_curr_1182_; 
v_curr_1182_ = lean_ctor_get(v_iter_1181_, 0);
lean_inc(v_curr_1182_);
return v_curr_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos___boxed(lean_object* v_iter_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(v_iter_1183_);
lean_dec_ref(v_iter_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(lean_object* v_iter_1185_){
_start:
{
lean_object* v_curr_1186_; lean_object* v_top_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1204_; 
v_curr_1186_ = lean_ctor_get(v_iter_1185_, 0);
v_top_1187_ = lean_ctor_get(v_iter_1185_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_iter_1185_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1189_ = v_iter_1185_;
v_isShared_1190_ = v_isSharedCheck_1204_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_top_1187_);
lean_inc(v_curr_1186_);
lean_dec(v_iter_1185_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1204_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_curr_1186_, v___x_1191_);
lean_dec(v_curr_1186_);
v___x_1193_ = lean_nat_dec_eq(v___x_1192_, v_top_1187_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1195_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_top_1187_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_dec(v___x_1192_);
v___x_1197_ = lean_unsigned_to_nat(2u);
v___x_1198_ = lean_nat_mul(v___x_1197_, v_top_1187_);
v___x_1199_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_1200_ = lean_nat_mul(v___x_1199_, v_top_1187_);
lean_dec(v_top_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1200_);
lean_ctor_set(v___x_1189_, 0, v___x_1198_);
v___x_1202_ = v___x_1189_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__0(lean_object* v_s_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_s_1205_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1(lean_object* v_toPure_1209_, lean_object* v_curr_1210_, lean_object* v_____r_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_apply_2(v_toPure_1209_, lean_box(0), v_curr_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2(lean_object* v_toPure_1213_, lean_object* v_modifyGet_1214_, lean_object* v___f_1215_, lean_object* v_toBind_1216_, lean_object* v_iter_1217_){
_start:
{
lean_object* v_curr_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_curr_1218_ = lean_ctor_get(v_iter_1217_, 0);
lean_inc(v_curr_1218_);
lean_dec_ref(v_iter_1217_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1219_, 0, v_toPure_1213_);
lean_closure_set(v___f_1219_, 1, v_curr_1218_);
v___x_1220_ = lean_apply_2(v_modifyGet_1214_, lean_box(0), v___f_1215_);
v___x_1221_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v___x_1220_, v___f_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_){
_start:
{
lean_object* v_toApplicative_1225_; lean_object* v_toBind_1226_; lean_object* v_get_1227_; lean_object* v_modifyGet_1228_; lean_object* v_toPure_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; 
v_toApplicative_1225_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_ref(v_toApplicative_1225_);
v_toBind_1226_ = lean_ctor_get(v_inst_1223_, 1);
lean_inc_n(v_toBind_1226_, 2);
lean_dec_ref(v_inst_1223_);
v_get_1227_ = lean_ctor_get(v_inst_1224_, 0);
lean_inc(v_get_1227_);
v_modifyGet_1228_ = lean_ctor_get(v_inst_1224_, 2);
lean_inc(v_modifyGet_1228_);
lean_dec_ref(v_inst_1224_);
v_toPure_1229_ = lean_ctor_get(v_toApplicative_1225_, 1);
lean_inc(v_toPure_1229_);
lean_dec_ref(v_toApplicative_1225_);
v___f_1230_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0));
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1231_, 0, v_toPure_1229_);
lean_closure_set(v___f_1231_, 1, v_modifyGet_1228_);
lean_closure_set(v___f_1231_, 2, v___f_1230_);
lean_closure_set(v___f_1231_, 3, v_toBind_1226_);
v___x_1232_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v_get_1227_, v___f_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos(lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(v_inst_1234_, v_inst_1235_);
return v___x_1236_;
}
}
lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default);
l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_SubExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
}
#ifdef __cplusplus
}
#endif
