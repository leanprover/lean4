// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Homo
// Imports: public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Sym.Simp.Attr import Lean.Meta.AppBuilder
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpExt(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "homoExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 68, 174, 250, 89, 27, 196, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "homoSourceTypesExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 10, 151, 10, 152, 93, 193, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoSourceTypesExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "invalid `[grind hom]` theorem, parameter `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "` is not determined by the left-hand side of the rule"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid `[grind hom]` theorem, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is conditional: hypothesis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 229, .m_capacity = 229, .m_length = 226, .m_data = "\nis not determined by the left-hand side and would have to be discharged when the rule is applied. Homomorphism rules must be unconditional; use E-matching attributes such as `[grind =]` or `[grind →]` for conditional theorems"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "invalid `[grind hom]` theorem, the source type of the `=`-injection rule `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is not headed by a constant"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "\nhomomorphism rules translate concrete types; generic injections cannot be tracked by the E-graph"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem = (const lean_object*)&l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "homoPredExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 129, 210, 121, 39, 93, 224, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoPredExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Tactic.Grind.Homo"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Grind.addHomoPredAttr"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "invalid `[grind hom_pred]` theorem, the conclusion of `"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "` does not contain an application whose trailing arguments are the theorem's explicit parameters"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "invalid `[grind hom_pred]` theorem, `"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 152, .m_capacity = 152, .m_length = 151, .m_data = "` must have at least one explicit parameter; the trigger is inferred from an application whose trailing arguments are the theorem's explicit parameters"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11;
static const lean_array_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a proposition"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_mkHomoPredInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkHomoPredInstances___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_13_;
v_res_13_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2____boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
return v_res_15_;
}
}
lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = l_Lean_Meta_Grind_homoExt;
v___x_19_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_18_, v_a_16_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getHomoTheorems___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_16_ = stack[0].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_16_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg___boxed(lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_21_);
lean_dec(v_a_21_);
return v_res_23_;
}
}
lean_object* l_Lean_Meta_Grind_getHomoTheorems(lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_25_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getHomoTheorems_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_24_ = stack[0].m_obj;
lean_object* v_a_25_ = stack[1].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Meta_Grind_getHomoTheorems(v_a_24_, v_a_25_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___boxed(lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Meta_Grind_getHomoTheorems(v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v_x_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v_a_34_);
lean_inc_ref_n(v___x_35_, 2);
v___x_36_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
lean_ctor_set(v___x_36_, 2, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_x_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v_x_37_, v_a_38_);
lean_dec_ref(v_x_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v___y_40_){
_start:
{
lean_inc(v___y_40_);
return v___y_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v___y_41_);
lean_dec(v___y_41_);
return v_res_42_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_52_ = lean_box(0);
v___x_53_ = 0;
v___f_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___f_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_56_ = l_Lean_NameSet_empty;
v___f_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_59_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___f_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
lean_ctor_set(v___x_59_, 3, v___f_55_);
lean_ctor_set(v___x_59_, 4, v___f_54_);
lean_ctor_set(v___x_59_, 5, v___x_52_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*6, v___x_53_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*6 + 1, v___x_53_);
return v___x_59_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_);
v___x_62_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_63_;
v_res_63_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
return v_res_65_;
}
}
lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_env_70_; lean_object* v___x_71_; lean_object* v_ext_72_; lean_object* v_toEnvExtension_73_; lean_object* v_asyncMode_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_68_ = lean_box(1);
v___x_69_ = lean_st_ref_get(v_a_66_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_70_);
lean_dec(v___x_69_);
v___x_71_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v_ext_72_ = lean_ctor_get(v___x_71_, 1);
v_toEnvExtension_73_ = lean_ctor_get(v_ext_72_, 0);
v_asyncMode_74_ = lean_ctor_get(v_toEnvExtension_73_, 2);
v___x_75_ = 0;
v___x_76_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_68_, v___x_71_, v_env_70_, v_asyncMode_74_, v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getHomoSourceTypes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_66_ = stack[0].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_66_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg___boxed(lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
lean_object* l_Lean_Meta_Grind_getHomoSourceTypes(lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_83_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getHomoSourceTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_82_ = stack[0].m_obj;
lean_object* v_a_83_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_Meta_Grind_getHomoSourceTypes(v_a_82_, v_a_83_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___boxed(lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_getHomoSourceTypes(v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_90_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(lean_object* v_k_91_, lean_object* v_b_92_, lean_object* v_c_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
lean_inc(v___y_97_);
lean_inc_ref(v___y_96_);
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
v___x_99_ = lean_apply_7(v_k_91_, v_b_92_, v_c_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, lean_box(0));
return v___x_99_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_91_ = stack[0].m_obj;
lean_object* v_b_92_ = stack[1].m_obj;
lean_object* v_c_93_ = stack[2].m_obj;
lean_object* v___y_94_ = stack[3].m_obj;
lean_object* v___y_95_ = stack[4].m_obj;
lean_object* v___y_96_ = stack[5].m_obj;
lean_object* v___y_97_ = stack[6].m_obj;
lean_object* v_res_100_;
v_res_100_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(v_k_91_, v_b_92_, v_c_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed(lean_object* v_k_101_, lean_object* v_b_102_, lean_object* v_c_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(v_k_101_, v_b_102_, v_c_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(lean_object* v_type_110_, lean_object* v_k_111_, uint8_t v_cleanupAnnotations_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___f_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___f_118_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_118_, 0, v_k_111_);
v___x_119_ = 0;
v___x_120_ = lean_box(0);
v___x_121_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_119_, v___x_120_, v_type_110_, v___f_118_, v_cleanupAnnotations_112_, v___x_119_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_121_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_121_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_110_ = stack[0].m_obj;
lean_object* v_k_111_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_112_ = stack[2].m_num;
lean_object* v___y_113_ = stack[3].m_obj;
lean_object* v___y_114_ = stack[4].m_obj;
lean_object* v___y_115_ = stack[5].m_obj;
lean_object* v___y_116_ = stack[6].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_110_, v_k_111_, v_cleanupAnnotations_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___boxed(lean_object* v_type_139_, lean_object* v_k_140_, lean_object* v_cleanupAnnotations_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_147_; lean_object* v_res_148_; 
v_cleanupAnnotations_boxed_147_ = lean_unbox(v_cleanupAnnotations_141_);
v_res_148_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_139_, v_k_140_, v_cleanupAnnotations_boxed_147_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_148_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_object* v_00_u03b1_149_, lean_object* v_type_150_, lean_object* v_k_151_, uint8_t v_cleanupAnnotations_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_150_, v_k_151_, v_cleanupAnnotations_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
return v___x_158_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_150_ = stack[1].m_obj;
lean_object* v_k_151_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_152_ = stack[3].m_num;
lean_object* v___y_153_ = stack[4].m_obj;
lean_object* v___y_154_ = stack[5].m_obj;
lean_object* v___y_155_ = stack[6].m_obj;
lean_object* v___y_156_ = stack[7].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_box(0), v_type_150_, v_k_151_, v_cleanupAnnotations_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___boxed(lean_object* v_00_u03b1_160_, lean_object* v_type_161_, lean_object* v_k_162_, lean_object* v_cleanupAnnotations_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_169_; lean_object* v_res_170_; 
v_cleanupAnnotations_boxed_169_ = lean_unbox(v_cleanupAnnotations_163_);
v_res_170_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(v_00_u03b1_160_, v_type_161_, v_k_162_, v_cleanupAnnotations_boxed_169_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_170_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(lean_object* v_k_171_, lean_object* v_t_172_){
_start:
{
if (lean_obj_tag(v_t_172_) == 0)
{
lean_object* v_k_173_; lean_object* v_l_174_; lean_object* v_r_175_; uint8_t v___x_176_; 
v_k_173_ = lean_ctor_get(v_t_172_, 1);
v_l_174_ = lean_ctor_get(v_t_172_, 3);
v_r_175_ = lean_ctor_get(v_t_172_, 4);
v___x_176_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_171_, v_k_173_);
switch(v___x_176_)
{
case 0:
{
v_t_172_ = v_l_174_;
goto _start;
}
case 1:
{
uint8_t v___x_178_; 
v___x_178_ = 1;
return v___x_178_;
}
default: 
{
v_t_172_ = v_r_175_;
goto _start;
}
}
}
else
{
uint8_t v___x_180_; 
v___x_180_ = 0;
return v___x_180_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_171_ = stack[0].m_obj;
lean_object* v_t_172_ = stack[1].m_obj;
uint8_t v_res_181_;
v_res_181_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_171_, v_t_172_);
stack->m_num = v_res_181_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg___boxed(lean_object* v_k_182_, lean_object* v_t_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_182_, v_t_183_);
lean_dec(v_t_183_);
lean_dec(v_k_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v_env_193_; uint8_t v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v_toCold_197_; lean_object* v_mctx_198_; lean_object* v_lctx_199_; lean_object* v_options_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_192_ = lean_st_ref_get(v___y_190_);
v_env_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_env_193_);
lean_dec(v___x_192_);
v___x_194_ = 0;
v_env_195_ = l_Lean_Environment_setRecordingDeps(v_env_193_, v___x_194_);
v___x_196_ = lean_st_ref_get(v___y_188_);
v_toCold_197_ = lean_ctor_get(v___y_189_, 0);
v_mctx_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_mctx_198_);
lean_dec(v___x_196_);
v_lctx_199_ = lean_ctor_get(v___y_187_, 2);
v_options_200_ = lean_ctor_get(v_toCold_197_, 2);
lean_inc_ref(v_options_200_);
lean_inc_ref(v_lctx_199_);
v___x_201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_201_, 0, v_env_195_);
lean_ctor_set(v___x_201_, 1, v_mctx_198_);
lean_ctor_set(v___x_201_, 2, v_lctx_199_);
lean_ctor_set(v___x_201_, 3, v_options_200_);
v___x_202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_msgData_186_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_186_ = stack[0].m_obj;
lean_object* v___y_187_ = stack[1].m_obj;
lean_object* v___y_188_ = stack[2].m_obj;
lean_object* v___y_189_ = stack[3].m_obj;
lean_object* v___y_190_ = stack[4].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msgData_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5___boxed(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msgData_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_ref_218_ = lean_ctor_get(v___y_215_, 2);
v___x_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msg_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_inc(v_ref_218_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_218_);
lean_ctor_set(v___x_224_, 1, v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_212_ = stack[0].m_obj;
lean_object* v___y_213_ = stack[1].m_obj;
lean_object* v___y_214_ = stack[2].m_obj;
lean_object* v___y_215_ = stack[3].m_obj;
lean_object* v___y_216_ = stack[4].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg___boxed(lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_236_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4));
v___x_245_ = l_Lean_stringToMessageData(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(lean_object* v___x_255_, lean_object* v_declName_256_, lean_object* v_as_257_, size_t v_sz_258_, size_t v_i_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_a_267_; uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_lt(v_i_259_, v_sz_258_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
lean_dec(v_declName_256_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v_b_260_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v_a_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v_a_274_ = lean_array_uget_borrowed(v_as_257_, v_i_259_);
v___x_275_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_a_274_, v___y_261_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; uint8_t v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = l_Lean_LocalDecl_binderInfo(v_a_276_);
lean_dec(v_a_276_);
if (v___x_277_ == 3)
{
v_a_267_ = v___x_273_;
goto v___jp_266_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = l_Lean_Expr_fvarId_x21(v_a_274_);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_278_, v___x_255_);
lean_dec(v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v_a_274_);
v___x_280_ = lean_infer_type(v_a_274_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_n(v_a_281_, 2);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_Lean_Meta_isProp(v_a_281_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; uint8_t v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = lean_unbox(v_a_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_a_281_);
v___x_285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1);
lean_inc(v_a_274_);
v___x_286_ = l_Lean_MessageData_ofExpr(v_a_274_);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_unbox(v_a_283_);
lean_dec(v_a_283_);
lean_inc(v_declName_256_);
v___x_291_ = l_Lean_MessageData_ofConstName(v_declName_256_, v___x_290_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_294_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_dec_ref_known(v___x_295_, 1);
v_a_267_ = v___x_273_;
goto v___jp_266_;
}
else
{
lean_dec(v_declName_256_);
return v___x_295_;
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_a_283_);
v___x_296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7);
lean_inc(v_declName_256_);
v___x_297_ = l_Lean_MessageData_ofConstName(v_declName_256_, v___x_279_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_indentExpr(v_a_281_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_304_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_dec_ref_known(v___x_305_, 1);
v_a_267_ = v___x_273_;
goto v___jp_266_;
}
else
{
lean_dec(v_declName_256_);
return v___x_305_;
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_a_281_);
lean_dec(v_declName_256_);
v_a_306_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_282_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_282_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_declName_256_);
v_a_314_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_280_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_280_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
v_a_267_ = v___x_273_;
goto v___jp_266_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_declName_256_);
v_a_322_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_275_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_275_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
v___jp_266_:
{
size_t v___x_268_; size_t v___x_269_; 
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_259_, v___x_268_);
v_i_259_ = v___x_269_;
v_b_260_ = v_a_267_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_255_ = stack[0].m_obj;
lean_object* v_declName_256_ = stack[1].m_obj;
lean_object* v_as_257_ = stack[2].m_obj;
size_t v_sz_258_ = stack[3].m_num;
size_t v_i_259_ = stack[4].m_num;
lean_object* v_b_260_ = stack[5].m_obj;
lean_object* v___y_261_ = stack[6].m_obj;
lean_object* v___y_262_ = stack[7].m_obj;
lean_object* v___y_263_ = stack[8].m_obj;
lean_object* v___y_264_ = stack[9].m_obj;
lean_object* v_res_330_;
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v___x_255_, v_declName_256_, v_as_257_, v_sz_258_, v_i_259_, v_b_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___boxed(lean_object* v___x_331_, lean_object* v_declName_332_, lean_object* v_as_333_, lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_343_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v___x_331_, v_declName_332_, v_as_333_, v_sz_boxed_342_, v_i_boxed_343_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_as_333_);
lean_dec(v___x_331_);
return v_res_344_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(lean_object* v___x_345_, lean_object* v_as_346_, size_t v_sz_347_, size_t v_i_348_, lean_object* v_b_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_lt(v_i_348_, v_sz_347_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v___x_345_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_b_349_);
return v___x_356_;
}
else
{
lean_object* v_fst_357_; lean_object* v_snd_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_393_; 
v_fst_357_ = lean_ctor_get(v_b_349_, 0);
v_snd_358_ = lean_ctor_get(v_b_349_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_b_349_);
if (v_isSharedCheck_393_ == 0)
{
v___x_360_ = v_b_349_;
v_isShared_361_ = v_isSharedCheck_393_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_snd_358_);
lean_inc(v_fst_357_);
lean_dec(v_b_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_393_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_array_uget_borrowed(v_as_346_, v_i_348_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
lean_inc(v___y_351_);
lean_inc_ref(v___y_350_);
lean_inc(v_a_362_);
v___x_363_ = lean_infer_type(v_a_362_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_384_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_384_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_384_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_384_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = l_Lean_Expr_fvarId_x21(v_a_362_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_375_, v_fst_357_);
lean_dec(v___x_375_);
if (v___x_376_ == 0)
{
lean_del_object(v___x_366_);
lean_dec(v_a_364_);
goto v___jp_368_;
}
else
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_Expr_containsFVar(v_a_364_, v___x_345_);
lean_dec(v_a_364_);
if (v___x_377_ == 0)
{
lean_del_object(v___x_366_);
goto v___jp_368_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
lean_del_object(v___x_360_);
lean_dec(v_snd_358_);
v___x_378_ = l_Lean_FVarIdSet_insert(v_fst_357_, v___x_345_);
v___x_379_ = lean_box(v___x_355_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_380_);
v___x_382_ = v___x_366_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
v___jp_368_:
{
lean_object* v___x_370_; 
if (v_isShared_361_ == 0)
{
v___x_370_ = v___x_360_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_357_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_snd_358_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
size_t v___x_371_; size_t v___x_372_; 
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_348_, v___x_371_);
v_i_348_ = v___x_372_;
v_b_349_ = v___x_370_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_del_object(v___x_360_);
lean_dec(v_snd_358_);
lean_dec(v_fst_357_);
lean_dec(v___x_345_);
v_a_385_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_363_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_363_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_345_ = stack[0].m_obj;
lean_object* v_as_346_ = stack[1].m_obj;
size_t v_sz_347_ = stack[2].m_num;
size_t v_i_348_ = stack[3].m_num;
lean_object* v_b_349_ = stack[4].m_obj;
lean_object* v___y_350_ = stack[5].m_obj;
lean_object* v___y_351_ = stack[6].m_obj;
lean_object* v___y_352_ = stack[7].m_obj;
lean_object* v___y_353_ = stack[8].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_345_, v_as_346_, v_sz_347_, v_i_348_, v_b_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1___boxed(lean_object* v___x_395_, lean_object* v_as_396_, lean_object* v_sz_397_, lean_object* v_i_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
size_t v_sz_boxed_405_; size_t v_i_boxed_406_; lean_object* v_res_407_; 
v_sz_boxed_405_ = lean_unbox_usize(v_sz_397_);
lean_dec(v_sz_397_);
v_i_boxed_406_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_395_, v_as_396_, v_sz_boxed_405_, v_i_boxed_406_, v_b_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec_ref(v_as_396_);
return v_res_407_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(lean_object* v_xs_408_, lean_object* v_as_409_, size_t v_sz_410_, size_t v_i_411_, lean_object* v_b_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_a_419_; uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_lt(v_i_411_, v_sz_410_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v_b_412_);
return v___x_424_;
}
else
{
lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_452_; 
v_fst_425_ = lean_ctor_get(v_b_412_, 0);
v_snd_426_ = lean_ctor_get(v_b_412_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_b_412_);
if (v_isSharedCheck_452_ == 0)
{
v___x_428_ = v_b_412_;
v_isShared_429_ = v_isSharedCheck_452_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_426_);
lean_inc(v_fst_425_);
lean_dec(v_b_412_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_452_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_a_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_a_430_ = lean_array_uget_borrowed(v_as_409_, v_i_411_);
v___x_431_ = l_Lean_Expr_fvarId_x21(v_a_430_);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_431_, v_fst_425_);
if (v___x_432_ == 0)
{
lean_object* v___x_434_; 
if (v_isShared_429_ == 0)
{
v___x_434_ = v___x_428_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_fst_425_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_snd_426_);
v___x_434_ = v_reuseFailAlloc_448_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
size_t v_sz_435_; size_t v___x_436_; lean_object* v___x_437_; 
v_sz_435_ = lean_array_size(v_xs_408_);
v___x_436_ = ((size_t)0ULL);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_431_, v_xs_408_, v_sz_435_, v___x_436_, v___x_434_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v_fst_439_ = lean_ctor_get(v_a_438_, 0);
v_snd_440_ = lean_ctor_get(v_a_438_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v_a_438_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_inc(v_fst_439_);
lean_dec(v_a_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_fst_439_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_snd_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
v_a_419_ = v___x_445_;
goto v___jp_418_;
}
}
}
else
{
return v___x_437_;
}
}
}
else
{
lean_object* v___x_450_; 
lean_dec(v___x_431_);
if (v_isShared_429_ == 0)
{
v___x_450_ = v___x_428_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_fst_425_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_426_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_419_ = v___x_450_;
goto v___jp_418_;
}
}
}
}
v___jp_418_:
{
size_t v___x_420_; size_t v___x_421_; 
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_411_, v___x_420_);
v_i_411_ = v___x_421_;
v_b_412_ = v_a_419_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_408_ = stack[0].m_obj;
lean_object* v_as_409_ = stack[1].m_obj;
size_t v_sz_410_ = stack[2].m_num;
size_t v_i_411_ = stack[3].m_num;
lean_object* v_b_412_ = stack[4].m_obj;
lean_object* v___y_413_ = stack[5].m_obj;
lean_object* v___y_414_ = stack[6].m_obj;
lean_object* v___y_415_ = stack[7].m_obj;
lean_object* v___y_416_ = stack[8].m_obj;
lean_object* v_res_453_;
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_408_, v_as_409_, v_sz_410_, v_i_411_, v_b_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2___boxed(lean_object* v_xs_454_, lean_object* v_as_455_, lean_object* v_sz_456_, lean_object* v_i_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_456_);
lean_dec(v_sz_456_);
v_i_boxed_465_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_454_, v_as_455_, v_sz_boxed_464_, v_i_boxed_465_, v_b_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec_ref(v_as_455_);
lean_dec_ref(v_xs_454_);
return v_res_466_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(lean_object* v_xs_467_, lean_object* v_a_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_snd_474_; uint8_t v___x_475_; 
v_snd_474_ = lean_ctor_get(v_a_468_, 1);
v___x_475_ = lean_unbox(v_snd_474_);
if (v___x_475_ == 0)
{
lean_object* v_fst_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_484_; 
lean_inc(v_snd_474_);
v_fst_476_ = lean_ctor_get(v_a_468_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_a_468_, 1);
lean_dec(v_unused_485_);
v___x_478_ = v_a_468_;
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_fst_476_);
lean_dec(v_a_468_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_fst_476_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_snd_474_);
v___x_481_ = v_reuseFailAlloc_483_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
}
else
{
lean_object* v_fst_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_509_; 
v_fst_486_ = lean_ctor_get(v_a_468_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_a_468_, 1);
lean_dec(v_unused_510_);
v___x_488_ = v_a_468_;
v_isShared_489_ = v_isSharedCheck_509_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_fst_486_);
lean_dec(v_a_468_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_509_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_490_ = 0;
v___x_491_ = lean_box(v___x_490_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_491_);
v___x_493_ = v___x_488_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_fst_486_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_508_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
size_t v_sz_494_; size_t v___x_495_; lean_object* v___x_496_; 
v_sz_494_ = lean_array_size(v_xs_467_);
v___x_495_ = ((size_t)0ULL);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_467_, v_xs_467_, v_sz_494_, v___x_495_, v___x_493_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v_fst_498_ = lean_ctor_get(v_a_497_, 0);
v_snd_499_ = lean_ctor_get(v_a_497_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v_a_497_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snd_499_);
lean_inc(v_fst_498_);
lean_dec(v_a_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_fst_498_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_snd_499_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v_a_468_ = v___x_504_;
goto _start;
}
}
}
else
{
return v___x_496_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_467_ = stack[0].m_obj;
lean_object* v_a_468_ = stack[1].m_obj;
lean_object* v___y_469_ = stack[2].m_obj;
lean_object* v___y_470_ = stack[3].m_obj;
lean_object* v___y_471_ = stack[4].m_obj;
lean_object* v___y_472_ = stack[5].m_obj;
lean_object* v_res_511_;
v_res_511_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_467_, v_a_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg___boxed(lean_object* v_xs_512_, lean_object* v_a_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_512_, v_a_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v_xs_512_);
return v_res_519_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(lean_object* v___y_520_, lean_object* v_as_521_, size_t v_sz_522_, size_t v_i_523_, lean_object* v_b_524_){
_start:
{
lean_object* v_a_527_; uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_523_, v_sz_522_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_b_524_);
return v___x_532_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_a_533_ = lean_array_uget_borrowed(v_as_521_, v_i_523_);
v___x_534_ = l_Lean_Expr_fvarId_x21(v_a_533_);
v___x_535_ = l_Lean_Expr_containsFVar(v___y_520_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec(v___x_534_);
v_a_527_ = v_b_524_;
goto v___jp_526_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_FVarIdSet_insert(v_b_524_, v___x_534_);
v_a_527_ = v___x_536_;
goto v___jp_526_;
}
}
v___jp_526_:
{
size_t v___x_528_; size_t v___x_529_; 
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_523_, v___x_528_);
v_i_523_ = v___x_529_;
v_b_524_ = v_a_527_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_520_ = stack[0].m_obj;
lean_object* v_as_521_ = stack[1].m_obj;
size_t v_sz_522_ = stack[2].m_num;
size_t v_i_523_ = stack[3].m_num;
lean_object* v_b_524_ = stack[4].m_obj;
lean_object* v_res_537_;
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_520_, v_as_521_, v_sz_522_, v_i_523_, v_b_524_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg___boxed(lean_object* v___y_538_, lean_object* v_as_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_b_542_, lean_object* v___y_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_545_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_538_, v_as_539_, v_sz_boxed_544_, v_i_boxed_545_, v_b_542_);
lean_dec_ref(v_as_539_);
lean_dec_ref(v___y_538_);
return v_res_546_;
}
}
lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0(lean_object* v___x_556_, lean_object* v_declName_557_, lean_object* v_xs_558_, lean_object* v_concl_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; uint8_t v___x_567_; lean_object* v___y_569_; 
lean_inc_ref(v_concl_559_);
v___x_565_ = l_Lean_Expr_cleanupAnnotations(v_concl_559_);
v___x_566_ = l_Lean_Expr_isApp(v___x_565_);
v___x_567_ = 1;
if (v___x_566_ == 0)
{
lean_dec_ref(v___x_565_);
v___y_569_ = v_concl_559_;
goto v___jp_568_;
}
else
{
lean_object* v_arg_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_arg_605_ = lean_ctor_get(v___x_565_, 1);
lean_inc_ref(v_arg_605_);
v___x_606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_565_);
v___x_607_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1));
v___x_608_ = l_Lean_Expr_isConstOf(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
lean_dec_ref(v_arg_605_);
v___x_609_ = l_Lean_Expr_isApp(v___x_606_);
if (v___x_609_ == 0)
{
lean_dec_ref(v___x_606_);
v___y_569_ = v_concl_559_;
goto v___jp_568_;
}
else
{
lean_object* v_arg_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_arg_610_ = lean_ctor_get(v___x_606_, 1);
lean_inc_ref(v_arg_610_);
v___x_611_ = l_Lean_Expr_appFnCleanup___redArg(v___x_606_);
v___x_612_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_613_ = l_Lean_Expr_isConstOf(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_Expr_isApp(v___x_611_);
if (v___x_614_ == 0)
{
lean_dec_ref(v___x_611_);
lean_dec_ref(v_arg_610_);
v___y_569_ = v_concl_559_;
goto v___jp_568_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_611_);
v___x_616_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_617_ = l_Lean_Expr_isConstOf(v___x_615_, v___x_616_);
lean_dec_ref(v___x_615_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_arg_610_);
v___y_569_ = v_concl_559_;
goto v___jp_568_;
}
else
{
lean_dec_ref(v_concl_559_);
v___y_569_ = v_arg_610_;
goto v___jp_568_;
}
}
}
else
{
lean_dec_ref(v___x_611_);
lean_dec_ref(v_concl_559_);
v___y_569_ = v_arg_610_;
goto v___jp_568_;
}
}
}
else
{
lean_dec_ref(v___x_606_);
lean_dec_ref(v_concl_559_);
v___y_569_ = v_arg_605_;
goto v___jp_568_;
}
}
v___jp_568_:
{
size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; 
v_sz_570_ = lean_array_size(v_xs_558_);
v___x_571_ = ((size_t)0ULL);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_569_, v_xs_558_, v_sz_570_, v___x_571_, v___x_556_);
lean_dec_ref(v___y_569_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_box(v___x_567_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_a_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_558_, v___x_575_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v_fst_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v_fst_578_ = lean_ctor_get(v_a_577_, 0);
lean_inc(v_fst_578_);
lean_dec(v_a_577_);
v___x_579_ = lean_box(0);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v_fst_578_, v_declName_557_, v_xs_558_, v_sz_570_, v___x_571_, v___x_579_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v_fst_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_588_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_579_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_579_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
return v___x_580_;
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_declName_557_);
v_a_589_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_576_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_576_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v_declName_557_);
v_a_597_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_572_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_572_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_validateHomoTheorem___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_556_ = stack[0].m_obj;
lean_object* v_declName_557_ = stack[1].m_obj;
lean_object* v_xs_558_ = stack[2].m_obj;
lean_object* v_concl_559_ = stack[3].m_obj;
lean_object* v___y_560_ = stack[4].m_obj;
lean_object* v___y_561_ = stack[5].m_obj;
lean_object* v___y_562_ = stack[6].m_obj;
lean_object* v___y_563_ = stack[7].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_Meta_Grind_validateHomoTheorem___lam__0(v___x_556_, v_declName_557_, v_xs_558_, v_concl_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed(lean_object* v___x_619_, lean_object* v_declName_620_, lean_object* v_xs_621_, lean_object* v_concl_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_Grind_validateHomoTheorem___lam__0(v___x_619_, v_declName_620_, v_xs_621_, v_concl_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_xs_621_);
return v_res_628_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(lean_object* v_ref_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_toCold_636_; lean_object* v_currRecDepth_637_; lean_object* v_ref_638_; uint16_t v_optionFlags_639_; uint8_t v_suppressElabErrors_640_; uint8_t v_isRecordingDeps_641_; lean_object* v_ref_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_toCold_636_ = lean_ctor_get(v___y_633_, 0);
v_currRecDepth_637_ = lean_ctor_get(v___y_633_, 1);
v_ref_638_ = lean_ctor_get(v___y_633_, 2);
v_optionFlags_639_ = lean_ctor_get_uint16(v___y_633_, sizeof(void*)*3);
v_suppressElabErrors_640_ = lean_ctor_get_uint8(v___y_633_, sizeof(void*)*3 + 2);
v_isRecordingDeps_641_ = lean_ctor_get_uint8(v___y_633_, sizeof(void*)*3 + 3);
v_ref_642_ = l_Lean_replaceRef(v_ref_629_, v_ref_638_);
lean_inc(v_currRecDepth_637_);
lean_inc_ref(v_toCold_636_);
v___x_643_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_643_, 0, v_toCold_636_);
lean_ctor_set(v___x_643_, 1, v_currRecDepth_637_);
lean_ctor_set(v___x_643_, 2, v_ref_642_);
lean_ctor_set_uint16(v___x_643_, sizeof(void*)*3, v_optionFlags_639_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*3 + 2, v_suppressElabErrors_640_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*3 + 3, v_isRecordingDeps_641_);
v___x_644_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_630_, v___y_631_, v___y_632_, v___x_643_, v___y_634_);
lean_dec_ref_known(v___x_643_, 3);
return v___x_644_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_629_ = stack[0].m_obj;
lean_object* v_msg_630_ = stack[1].m_obj;
lean_object* v___y_631_ = stack[2].m_obj;
lean_object* v___y_632_ = stack[3].m_obj;
lean_object* v___y_633_ = stack[4].m_obj;
lean_object* v___y_634_ = stack[5].m_obj;
lean_object* v_res_645_;
v_res_645_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_629_, v_msg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg___boxed(lean_object* v_ref_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_646_, v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v_ref_646_);
return v_res_653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
lean_ctor_set(v___x_660_, 2, v___x_659_);
lean_ctor_set(v___x_660_, 3, v___x_659_);
lean_ctor_set(v___x_660_, 4, v___x_658_);
lean_ctor_set(v___x_660_, 5, v___x_658_);
lean_ctor_set(v___x_660_, 6, v___x_658_);
lean_ctor_set(v___x_660_, 7, v___x_658_);
lean_ctor_set(v___x_660_, 8, v___x_658_);
lean_ctor_set(v___x_660_, 9, v___x_658_);
lean_ctor_set(v___x_660_, 10, v___x_658_);
lean_ctor_set(v___x_660_, 11, v___x_657_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_unsigned_to_nat(32u);
v___x_662_ = lean_mk_empty_array_with_capacity(v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_664_ = ((size_t)5ULL);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_unsigned_to_nat(32u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_669_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
lean_ctor_set(v___x_669_, 2, v___x_665_);
lean_ctor_set(v___x_669_, 3, v___x_665_);
lean_ctor_set_usize(v___x_669_, 4, v___x_664_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_box(1);
v___x_671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_670_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__21(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__20));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__23(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__22));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__25(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__24));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__27(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__26));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_707_, lean_object* v_declHint_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_env_713_; uint8_t v___x_714_; 
v___x_711_ = lean_box(0);
v___x_712_ = lean_st_ref_get(v___y_709_);
v_env_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_ref(v_env_713_);
lean_dec(v___x_712_);
v___x_714_ = l_Lean_Name_isAnonymous(v_declHint_708_);
if (v___x_714_ == 0)
{
uint8_t v_isExporting_715_; 
v_isExporting_715_ = lean_ctor_get_uint8(v_env_713_, sizeof(void*)*13);
if (v_isExporting_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_708_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_msg_707_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; uint8_t v___x_718_; 
lean_inc_ref(v_env_713_);
v___x_717_ = l_Lean_Environment_setExporting(v_env_713_, v___x_714_);
lean_inc(v_declHint_708_);
lean_inc_ref(v___x_717_);
v___x_718_ = l_Lean_Environment_contains(v___x_717_, v_declHint_708_, v_isExporting_715_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_708_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v_msg_707_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_c_725_; lean_object* v___x_726_; 
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_721_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_722_ = l_Lean_Options_empty;
v___x_723_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_723_, 0, v___x_717_);
lean_ctor_set(v___x_723_, 1, v___x_720_);
lean_ctor_set(v___x_723_, 2, v___x_721_);
lean_ctor_set(v___x_723_, 3, v___x_722_);
lean_inc(v_declHint_708_);
v___x_724_ = l_Lean_MessageData_ofConstName(v_declHint_708_, v___x_714_);
v_c_725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_725_, 0, v___x_723_);
lean_ctor_set(v_c_725_, 1, v___x_724_);
v___x_726_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_713_, v_declHint_708_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_708_);
v___x_727_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_c_725_);
v___x_729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_MessageData_note(v___x_730_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v_msg_707_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_790_; 
v_val_734_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_790_ == 0)
{
v___x_736_ = v___x_726_;
v_isShared_737_ = v_isSharedCheck_790_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v___x_726_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_790_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v_modules_739_; lean_object* v_moduleNames_740_; lean_object* v_mod_741_; uint8_t v___y_743_; uint8_t v___x_773_; 
v___x_738_ = l_Lean_Environment_header(v_env_713_);
lean_dec_ref(v_env_713_);
v_modules_739_ = lean_ctor_get(v___x_738_, 3);
lean_inc_ref(v_modules_739_);
v_moduleNames_740_ = lean_ctor_get(v___x_738_, 4);
lean_inc_ref(v_moduleNames_740_);
lean_dec_ref(v___x_738_);
v_mod_741_ = lean_array_get(v___x_711_, v_moduleNames_740_, v_val_734_);
lean_dec_ref(v_moduleNames_740_);
v___x_773_ = l_Lean_isPrivateName(v_declHint_708_);
lean_dec(v_declHint_708_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_modules_739_);
v___x_775_ = lean_nat_dec_lt(v_val_734_, v___x_774_);
if (v___x_775_ == 0)
{
lean_dec_ref(v_modules_739_);
lean_dec(v_val_734_);
v___y_743_ = v___x_773_;
goto v___jp_742_;
}
else
{
lean_object* v___x_776_; lean_object* v_toImport_777_; uint8_t v_isExported_778_; 
v___x_776_ = lean_array_fget(v_modules_739_, v_val_734_);
lean_dec(v_val_734_);
lean_dec_ref(v_modules_739_);
v_toImport_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc_ref(v_toImport_777_);
lean_dec(v___x_776_);
v_isExported_778_ = lean_ctor_get_uint8(v_toImport_777_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_777_);
v___y_743_ = v_isExported_778_;
goto v___jp_742_;
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v_modules_739_);
lean_del_object(v___x_736_);
lean_dec(v_val_734_);
v___x_779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_c_725_);
v___x_781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__25);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_MessageData_ofName(v_mod_741_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__27);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_MessageData_note(v___x_786_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v_msg_707_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
v___jp_742_:
{
if (v___y_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v_c_725_);
v___x_746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_MessageData_ofName(v_mod_741_);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_MessageData_note(v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v_msg_707_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v___x_753_);
v___x_755_ = v___x_736_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_c_725_);
v___x_759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_MessageData_ofName(v_mod_741_);
lean_inc_ref(v___x_761_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__21);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_761_);
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__23);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_MessageData_note(v___x_767_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v_msg_707_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v___x_769_);
v___x_771_ = v___x_736_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_791_; 
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_708_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_msg_707_);
return v___x_791_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_707_ = stack[0].m_obj;
lean_object* v_declHint_708_ = stack[1].m_obj;
lean_object* v___y_709_ = stack[2].m_obj;
lean_object* v_res_792_;
v_res_792_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_707_, v_declHint_708_, v___y_709_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_793_, lean_object* v_declHint_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_793_, v_declHint_794_, v___y_795_);
lean_dec(v___y_795_);
return v_res_797_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_798_, lean_object* v_declHint_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
v___x_805_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_798_, v_declHint_799_, v___y_803_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_815_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = l_Lean_unknownIdentifierMessageTag;
v___x_811_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_a_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_798_ = stack[0].m_obj;
lean_object* v_declHint_799_ = stack[1].m_obj;
lean_object* v___y_800_ = stack[2].m_obj;
lean_object* v___y_801_ = stack[3].m_obj;
lean_object* v___y_802_ = stack[4].m_obj;
lean_object* v___y_803_ = stack[5].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_798_, v_declHint_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_817_, lean_object* v_declHint_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_817_, v_declHint_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_824_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(lean_object* v_ref_825_, lean_object* v_msg_826_, lean_object* v_declHint_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_835_; 
v___x_833_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_826_, v_declHint_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v___x_833_);
v___x_835_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_825_, v_a_834_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
return v___x_835_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_825_ = stack[0].m_obj;
lean_object* v_msg_826_ = stack[1].m_obj;
lean_object* v_declHint_827_ = stack[2].m_obj;
lean_object* v___y_828_ = stack[3].m_obj;
lean_object* v___y_829_ = stack[4].m_obj;
lean_object* v___y_830_ = stack[5].m_obj;
lean_object* v___y_831_ = stack[6].m_obj;
lean_object* v_res_836_;
v_res_836_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_825_, v_msg_826_, v_declHint_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_ref_837_, lean_object* v_msg_838_, lean_object* v_declHint_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_837_, v_msg_838_, v_declHint_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v_ref_837_);
return v_res_845_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0));
v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2));
v___x_851_ = l_Lean_stringToMessageData(v___x_850_);
return v___x_851_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_852_, lean_object* v_constName_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_859_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1);
v___x_860_ = 0;
lean_inc(v_constName_853_);
v___x_861_ = l_Lean_MessageData_ofConstName(v_constName_853_, v___x_860_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_859_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_852_, v___x_864_, v_constName_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
return v___x_865_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_852_ = stack[0].m_obj;
lean_object* v_constName_853_ = stack[1].m_obj;
lean_object* v___y_854_ = stack[2].m_obj;
lean_object* v___y_855_ = stack[3].m_obj;
lean_object* v___y_856_ = stack[4].m_obj;
lean_object* v___y_857_ = stack[5].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_852_, v_constName_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_867_, lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_867_, v_constName_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v_ref_867_);
return v_res_874_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_ref_881_; lean_object* v___x_882_; 
v_ref_881_ = lean_ctor_get(v___y_878_, 2);
v___x_882_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_881_, v_constName_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_882_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_875_ = stack[0].m_obj;
lean_object* v___y_876_ = stack[1].m_obj;
lean_object* v___y_877_ = stack[2].m_obj;
lean_object* v___y_878_ = stack[3].m_obj;
lean_object* v___y_879_ = stack[4].m_obj;
lean_object* v_res_883_;
v_res_883_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg___boxed(lean_object* v_constName_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_890_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(lean_object* v_constName_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; lean_object* v_env_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
v___x_897_ = lean_st_ref_get(v___y_895_);
v_env_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_env_898_);
lean_dec(v___x_897_);
v___x_899_ = 0;
lean_inc(v_constName_891_);
v___x_900_ = l_Lean_Environment_find_x3f(v_env_898_, v_constName_891_, v___x_899_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_constName_891_);
v_val_902_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 0);
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_val_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_891_ = stack[0].m_obj;
lean_object* v___y_892_ = stack[1].m_obj;
lean_object* v___y_893_ = stack[2].m_obj;
lean_object* v___y_894_ = stack[3].m_obj;
lean_object* v___y_895_ = stack[4].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_constName_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7___boxed(lean_object* v_constName_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_constName_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
lean_object* l_Lean_Meta_Grind_validateHomoTheorem(lean_object* v_declName_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; 
v___x_924_ = lean_box(1);
lean_inc(v_declName_918_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed), 9, 2);
lean_closure_set(v___f_925_, 0, v___x_924_);
lean_closure_set(v___f_925_, 1, v_declName_918_);
v___x_926_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_Lean_ConstantInfo_type(v_a_927_);
lean_dec(v_a_927_);
v___x_929_ = 0;
v___x_930_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_928_, v___f_925_, v___x_929_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_930_;
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v___f_925_);
v_a_931_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_926_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_926_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_validateHomoTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_918_ = stack[0].m_obj;
lean_object* v_a_919_ = stack[1].m_obj;
lean_object* v_a_920_ = stack[2].m_obj;
lean_object* v_a_921_ = stack[3].m_obj;
lean_object* v_a_922_ = stack[4].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object* v_declName_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_946_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_object* v_00_u03b2_947_, lean_object* v_k_948_, lean_object* v_t_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_948_, v_t_949_);
return v___x_950_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_948_ = stack[1].m_obj;
lean_object* v_t_949_ = stack[2].m_obj;
uint8_t v_res_951_;
v_res_951_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_box(0), v_k_948_, v_t_949_);
stack->m_num = v_res_951_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___boxed(lean_object* v_00_u03b2_952_, lean_object* v_k_953_, lean_object* v_t_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(v_00_u03b2_952_, v_k_953_, v_t_954_);
lean_dec(v_t_954_);
lean_dec(v_k_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(lean_object* v___y_957_, lean_object* v_as_958_, size_t v_sz_959_, size_t v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_957_, v_as_958_, v_sz_959_, v_i_960_, v_b_961_);
return v___x_967_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_957_ = stack[0].m_obj;
lean_object* v_as_958_ = stack[1].m_obj;
size_t v_sz_959_ = stack[2].m_num;
size_t v_i_960_ = stack[3].m_num;
lean_object* v_b_961_ = stack[4].m_obj;
lean_object* v___y_962_ = stack[5].m_obj;
lean_object* v___y_963_ = stack[6].m_obj;
lean_object* v___y_964_ = stack[7].m_obj;
lean_object* v___y_965_ = stack[8].m_obj;
lean_object* v_res_968_;
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(v___y_957_, v_as_958_, v_sz_959_, v_i_960_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___boxed(lean_object* v___y_969_, lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v_sz_boxed_979_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_980_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(v___y_969_, v_as_970_, v_sz_boxed_979_, v_i_boxed_980_, v_b_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_as_970_);
lean_dec_ref(v___y_969_);
return v_res_981_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(lean_object* v_xs_982_, lean_object* v_inst_983_, lean_object* v_a_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_982_, v_a_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_982_ = stack[0].m_obj;
lean_object* v_a_984_ = stack[2].m_obj;
lean_object* v___y_985_ = stack[3].m_obj;
lean_object* v___y_986_ = stack[4].m_obj;
lean_object* v___y_987_ = stack[5].m_obj;
lean_object* v___y_988_ = stack[6].m_obj;
lean_object* v_res_991_;
v_res_991_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(v_xs_982_, lean_box(0), v_a_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___boxed(lean_object* v_xs_992_, lean_object* v_inst_993_, lean_object* v_a_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(v_xs_992_, v_inst_993_, v_a_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_xs_992_);
return v_res_1000_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_object* v_00_u03b1_1001_, lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1002_ = stack[1].m_obj;
lean_object* v___y_1003_ = stack[2].m_obj;
lean_object* v___y_1004_ = stack[3].m_obj;
lean_object* v___y_1005_ = stack[4].m_obj;
lean_object* v___y_1006_ = stack[5].m_obj;
lean_object* v_res_1009_;
v_res_1009_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_box(0), v_msg_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
stack->m_obj
 = v_res_1009_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(v_00_u03b1_1010_, v_msg_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_object* v_00_u03b1_1018_, lean_object* v_constName_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1019_ = stack[1].m_obj;
lean_object* v___y_1020_ = stack[2].m_obj;
lean_object* v___y_1021_ = stack[3].m_obj;
lean_object* v___y_1022_ = stack[4].m_obj;
lean_object* v___y_1023_ = stack[5].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_box(0), v_constName_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_constName_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(v_00_u03b1_1027_, v_constName_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_1035_, lean_object* v_ref_1036_, lean_object* v_constName_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_1036_, v_constName_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1036_ = stack[1].m_obj;
lean_object* v_constName_1037_ = stack[2].m_obj;
lean_object* v___y_1038_ = stack[3].m_obj;
lean_object* v___y_1039_ = stack[4].m_obj;
lean_object* v___y_1040_ = stack[5].m_obj;
lean_object* v___y_1041_ = stack[6].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_box(0), v_ref_1036_, v_constName_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_ref_1046_, lean_object* v_constName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(v_00_u03b1_1045_, v_ref_1046_, v_constName_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v_ref_1046_);
return v_res_1053_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_object* v_00_u03b1_1054_, lean_object* v_ref_1055_, lean_object* v_msg_1056_, lean_object* v_declHint_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_1055_, v_msg_1056_, v_declHint_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1055_ = stack[1].m_obj;
lean_object* v_msg_1056_ = stack[2].m_obj;
lean_object* v_declHint_1057_ = stack[3].m_obj;
lean_object* v___y_1058_ = stack[4].m_obj;
lean_object* v___y_1059_ = stack[5].m_obj;
lean_object* v___y_1060_ = stack[6].m_obj;
lean_object* v___y_1061_ = stack[7].m_obj;
lean_object* v_res_1064_;
v_res_1064_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_box(0), v_ref_1055_, v_msg_1056_, v_declHint_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
stack->m_obj
 = v_res_1064_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_ref_1066_, lean_object* v_msg_1067_, lean_object* v_declHint_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(v_00_u03b1_1065_, v_ref_1066_, v_msg_1067_, v_declHint_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_ref_1066_);
return v_res_1074_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(lean_object* v_msg_1075_, lean_object* v_declHint_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_1075_, v_declHint_1076_, v___y_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1075_ = stack[0].m_obj;
lean_object* v_declHint_1076_ = stack[1].m_obj;
lean_object* v___y_1077_ = stack[2].m_obj;
lean_object* v___y_1078_ = stack[3].m_obj;
lean_object* v___y_1079_ = stack[4].m_obj;
lean_object* v___y_1080_ = stack[5].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(v_msg_1075_, v_declHint_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1084_, lean_object* v_declHint_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(v_msg_1084_, v_declHint_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_object* v_00_u03b1_1092_, lean_object* v_ref_1093_, lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_1093_, v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1093_ = stack[1].m_obj;
lean_object* v_msg_1094_ = stack[2].m_obj;
lean_object* v___y_1095_ = stack[3].m_obj;
lean_object* v___y_1096_ = stack[4].m_obj;
lean_object* v___y_1097_ = stack[5].m_obj;
lean_object* v___y_1098_ = stack[6].m_obj;
lean_object* v_res_1101_;
v_res_1101_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_box(0), v_ref_1093_, v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
stack->m_obj
 = v_res_1101_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1102_, lean_object* v_ref_1103_, lean_object* v_msg_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(v_00_u03b1_1102_, v_ref_1103_, v_msg_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v_ref_1103_);
return v_res_1110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(lean_object* v_declName_1120_, lean_object* v_x_1121_, lean_object* v_concl_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___y_1132_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
lean_inc_ref(v_concl_1122_);
v___x_1158_ = l_Lean_Expr_cleanupAnnotations(v_concl_1122_);
v___x_1159_ = l_Lean_Expr_isApp(v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec_ref(v___x_1158_);
v___y_1132_ = v_concl_1122_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1158_);
v___x_1161_ = l_Lean_Expr_isApp(v___x_1160_);
if (v___x_1161_ == 0)
{
lean_dec_ref(v___x_1160_);
v___y_1132_ = v_concl_1122_;
goto v___jp_1131_;
}
else
{
lean_object* v_arg_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_arg_1162_ = lean_ctor_get(v___x_1160_, 1);
lean_inc_ref(v_arg_1162_);
v___x_1163_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1160_);
v___x_1164_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_1165_ = l_Lean_Expr_isConstOf(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; 
v___x_1166_ = l_Lean_Expr_isApp(v___x_1163_);
if (v___x_1166_ == 0)
{
lean_dec_ref(v___x_1163_);
lean_dec_ref(v_arg_1162_);
v___y_1132_ = v_concl_1122_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1163_);
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1169_ = l_Lean_Expr_isConstOf(v___x_1167_, v___x_1168_);
lean_dec_ref(v___x_1167_);
if (v___x_1169_ == 0)
{
lean_dec_ref(v_arg_1162_);
v___y_1132_ = v_concl_1122_;
goto v___jp_1131_;
}
else
{
lean_dec_ref(v_concl_1122_);
v___y_1132_ = v_arg_1162_;
goto v___jp_1131_;
}
}
}
else
{
lean_dec_ref(v___x_1163_);
lean_dec_ref(v_concl_1122_);
v___y_1132_ = v_arg_1162_;
goto v___jp_1131_;
}
}
}
v___jp_1128_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
v___jp_1131_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = l_Lean_Expr_cleanupAnnotations(v___y_1132_);
v___x_1134_ = l_Lean_Expr_isApp(v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v___x_1133_);
lean_dec(v_declName_1120_);
goto v___jp_1128_;
}
else
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1133_);
v___x_1136_ = l_Lean_Expr_isApp(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v___x_1135_);
lean_dec(v_declName_1120_);
goto v___jp_1128_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1135_);
v___x_1138_ = l_Lean_Expr_isApp(v___x_1137_);
if (v___x_1138_ == 0)
{
lean_dec_ref(v___x_1137_);
lean_dec(v_declName_1120_);
goto v___jp_1128_;
}
else
{
lean_object* v_arg_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_arg_1139_ = lean_ctor_get(v___x_1137_, 1);
lean_inc_ref(v_arg_1139_);
v___x_1140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1137_);
v___x_1141_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1142_ = l_Lean_Expr_isConstOf(v___x_1140_, v___x_1141_);
lean_dec_ref(v___x_1140_);
if (v___x_1142_ == 0)
{
lean_dec_ref(v_arg_1139_);
lean_dec(v_declName_1120_);
goto v___jp_1128_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Expr_getAppFn(v_arg_1139_);
if (lean_obj_tag(v___x_1143_) == 4)
{
lean_object* v_declName_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_arg_1139_);
lean_dec(v_declName_1120_);
v_declName_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_declName_1144_);
lean_dec_ref_known(v___x_1143_, 2);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_declName_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v___x_1143_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1);
v___x_1148_ = 0;
v___x_1149_ = l_Lean_MessageData_ofConstName(v_declName_1120_, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1147_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_indentExpr(v_arg_1139_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1156_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1157_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1120_ = stack[0].m_obj;
lean_object* v_x_1121_ = stack[1].m_obj;
lean_object* v_concl_1122_ = stack[2].m_obj;
lean_object* v___y_1123_ = stack[3].m_obj;
lean_object* v___y_1124_ = stack[4].m_obj;
lean_object* v___y_1125_ = stack[5].m_obj;
lean_object* v___y_1126_ = stack[6].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(v_declName_1120_, v_x_1121_, v_concl_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed(lean_object* v_declName_1171_, lean_object* v_x_1172_, lean_object* v_concl_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(v_declName_1171_, v_x_1172_, v_concl_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec_ref(v_x_1172_);
return v_res_1179_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(lean_object* v_declName_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___f_1186_; lean_object* v___x_1187_; 
lean_inc(v_declName_1180_);
v___f_1186_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1186_, 0, v_declName_1180_);
v___x_1187_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l_Lean_ConstantInfo_type(v_a_1188_);
lean_dec(v_a_1188_);
v___x_1190_ = 0;
v___x_1191_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1189_, v___f_1186_, v___x_1190_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
return v___x_1191_;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v___f_1186_);
v_a_1192_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1187_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1187_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1180_ = stack[0].m_obj;
lean_object* v_a_1181_ = stack[1].m_obj;
lean_object* v_a_1182_ = stack[2].m_obj;
lean_object* v_a_1183_ = stack[3].m_obj;
lean_object* v_a_1184_ = stack[4].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___boxed(lean_object* v_declName_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1207_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1213_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
lean_ctor_set(v___x_1213_, 2, v___x_1212_);
lean_ctor_set(v___x_1213_, 3, v___x_1212_);
lean_ctor_set(v___x_1213_, 4, v___x_1212_);
lean_ctor_set(v___x_1213_, 5, v___x_1212_);
return v___x_1213_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object* v_ext_1214_, lean_object* v_b_1215_, uint8_t v_kind_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_toCold_1221_; lean_object* v_currNamespace_1222_; lean_object* v___x_1223_; lean_object* v_env_1224_; lean_object* v_nextMacroScope_1225_; lean_object* v_ngen_1226_; lean_object* v_auxDeclNGen_1227_; lean_object* v_traceState_1228_; lean_object* v_recordedDeps_1229_; lean_object* v_messages_1230_; lean_object* v_infoState_1231_; lean_object* v_snapshotTasks_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1259_; 
v_toCold_1221_ = lean_ctor_get(v___y_1218_, 0);
v_currNamespace_1222_ = lean_ctor_get(v_toCold_1221_, 4);
v___x_1223_ = lean_st_ref_take(v___y_1219_);
v_env_1224_ = lean_ctor_get(v___x_1223_, 0);
v_nextMacroScope_1225_ = lean_ctor_get(v___x_1223_, 1);
v_ngen_1226_ = lean_ctor_get(v___x_1223_, 2);
v_auxDeclNGen_1227_ = lean_ctor_get(v___x_1223_, 3);
v_traceState_1228_ = lean_ctor_get(v___x_1223_, 4);
v_recordedDeps_1229_ = lean_ctor_get(v___x_1223_, 6);
v_messages_1230_ = lean_ctor_get(v___x_1223_, 7);
v_infoState_1231_ = lean_ctor_get(v___x_1223_, 8);
v_snapshotTasks_1232_ = lean_ctor_get(v___x_1223_, 9);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1223_, 5);
lean_dec(v_unused_1260_);
v___x_1234_ = v___x_1223_;
v_isShared_1235_ = v_isSharedCheck_1259_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snapshotTasks_1232_);
lean_inc(v_infoState_1231_);
lean_inc(v_messages_1230_);
lean_inc(v_recordedDeps_1229_);
lean_inc(v_traceState_1228_);
lean_inc(v_auxDeclNGen_1227_);
lean_inc(v_ngen_1226_);
lean_inc(v_nextMacroScope_1225_);
lean_inc(v_env_1224_);
lean_dec(v___x_1223_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1259_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_inc(v_currNamespace_1222_);
v___x_1236_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1224_, v_ext_1214_, v_b_1215_, v_kind_1216_, v_currNamespace_1222_);
v___x_1237_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 5, v___x_1237_);
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_nextMacroScope_1225_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_ngen_1226_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_auxDeclNGen_1227_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_traceState_1228_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1258_, 6, v_recordedDeps_1229_);
lean_ctor_set(v_reuseFailAlloc_1258_, 7, v_messages_1230_);
lean_ctor_set(v_reuseFailAlloc_1258_, 8, v_infoState_1231_);
lean_ctor_set(v_reuseFailAlloc_1258_, 9, v_snapshotTasks_1232_);
v___x_1239_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_mctx_1242_; lean_object* v_zetaDeltaFVarIds_1243_; lean_object* v_postponed_1244_; lean_object* v_diag_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1256_; 
v___x_1240_ = lean_st_ref_put(v___y_1219_, v___x_1239_);
v___x_1241_ = lean_st_ref_take(v___y_1217_);
v_mctx_1242_ = lean_ctor_get(v___x_1241_, 0);
v_zetaDeltaFVarIds_1243_ = lean_ctor_get(v___x_1241_, 2);
v_postponed_1244_ = lean_ctor_get(v___x_1241_, 3);
v_diag_1245_ = lean_ctor_get(v___x_1241_, 4);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1241_, 1);
lean_dec(v_unused_1257_);
v___x_1247_ = v___x_1241_;
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_diag_1245_);
lean_inc(v_postponed_1244_);
lean_inc(v_zetaDeltaFVarIds_1243_);
lean_inc(v_mctx_1242_);
lean_dec(v___x_1241_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_mctx_1242_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_zetaDeltaFVarIds_1243_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_postponed_1244_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_diag_1245_);
v___x_1252_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_st_ref_put(v___y_1217_, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1249_);
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1214_ = stack[0].m_obj;
lean_object* v_b_1215_ = stack[1].m_obj;
uint8_t v_kind_1216_ = stack[2].m_num;
lean_object* v___y_1217_ = stack[3].m_obj;
lean_object* v___y_1218_ = stack[4].m_obj;
lean_object* v___y_1219_ = stack[5].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1214_, v_b_1215_, v_kind_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object* v_ext_1262_, lean_object* v_b_1263_, lean_object* v_kind_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
uint8_t v_kind_boxed_1269_; lean_object* v_res_1270_; 
v_kind_boxed_1269_ = lean_unbox(v_kind_1264_);
v_res_1270_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1262_, v_b_1263_, v_kind_boxed_1269_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
return v_res_1270_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_00_u03c3_1273_, lean_object* v_ext_1274_, lean_object* v_b_1275_, uint8_t v_kind_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1274_, v_b_1275_, v_kind_1276_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1274_ = stack[3].m_obj;
lean_object* v_b_1275_ = stack[4].m_obj;
uint8_t v_kind_1276_ = stack[5].m_num;
lean_object* v___y_1277_ = stack[6].m_obj;
lean_object* v___y_1278_ = stack[7].m_obj;
lean_object* v___y_1279_ = stack[8].m_obj;
lean_object* v___y_1280_ = stack[9].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_box(0), lean_box(0), lean_box(0), v_ext_1274_, v_b_1275_, v_kind_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_00_u03c3_1286_, lean_object* v_ext_1287_, lean_object* v_b_1288_, lean_object* v_kind_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v_kind_boxed_1295_; lean_object* v_res_1296_; 
v_kind_boxed_1295_ = lean_unbox(v_kind_1289_);
v_res_1296_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(v_00_u03b1_1284_, v_00_u03b2_1285_, v_00_u03c3_1286_, v_ext_1287_, v_b_1288_, v_kind_boxed_1295_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1296_;
}
}
lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t v_attrKind_1297_, lean_object* v_declName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
lean_inc(v_declName_1298_);
v___x_1304_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref_known(v___x_1304_, 1);
v___x_1305_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1317_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1317_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1317_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
if (lean_obj_tag(v_a_1306_) == 1)
{
lean_object* v_val_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_del_object(v___x_1308_);
v_val_1310_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_a_1306_, 1);
v___x_1311_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v___x_1312_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1311_, v_val_1310_, v_attrKind_1297_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_dec(v_a_1306_);
v___x_1313_ = lean_box(0);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1313_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1305_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1305_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_dec(v_declName_1298_);
return v___x_1304_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addHomoAttr___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_attrKind_1297_ = stack[0].m_num;
lean_object* v_declName_1298_ = stack[1].m_obj;
lean_object* v___y_1299_ = stack[2].m_obj;
lean_object* v___y_1300_ = stack[3].m_obj;
lean_object* v___y_1301_ = stack[4].m_obj;
lean_object* v___y_1302_ = stack[5].m_obj;
lean_object* v_res_1326_;
v_res_1326_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_1297_, v_declName_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
stack->m_obj
 = v_res_1326_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object* v_attrKind_1327_, lean_object* v_declName_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v_attrKind_boxed_1334_; lean_object* v_res_1335_; 
v_attrKind_boxed_1334_ = lean_unbox(v_attrKind_1327_);
v_res_1335_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_boxed_1334_, v_declName_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1335_;
}
}
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object* v_declName_1336_, uint8_t v_attrKind_1337_, uint8_t v_fallback_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v_validate_1345_; 
v___x_1344_ = lean_box(v_attrKind_1337_);
v_validate_1345_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed), 7, 1);
lean_closure_set(v_validate_1345_, 0, v___x_1344_);
if (v_fallback_1338_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = l_Lean_Meta_Grind_homoExt;
v___x_1347_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v___x_1346_, v_declName_1336_, v_attrKind_1337_, v_validate_1345_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v_validate_1345_);
lean_inc(v_declName_1336_);
v___x_1348_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_1337_, v_declName_1336_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1348_, 1);
v___x_1349_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_1336_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v_expr_1351_; lean_object* v_pattern_1352_; lean_object* v_rhs_1353_; uint8_t v_perm_1354_; lean_object* v_rhsVarMask_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1364_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v_expr_1351_ = lean_ctor_get(v_a_1350_, 0);
v_pattern_1352_ = lean_ctor_get(v_a_1350_, 1);
v_rhs_1353_ = lean_ctor_get(v_a_1350_, 2);
v_perm_1354_ = lean_ctor_get_uint8(v_a_1350_, sizeof(void*)*4);
v_rhsVarMask_1355_ = lean_ctor_get(v_a_1350_, 3);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1357_ = v_a_1350_;
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_rhsVarMask_1355_);
lean_inc(v_rhs_1353_);
lean_inc(v_pattern_1352_);
lean_inc(v_expr_1351_);
lean_dec(v_a_1350_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = l_Lean_Meta_Grind_homoExt;
if (v_isShared_1358_ == 0)
{
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_expr_1351_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_pattern_1352_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_rhs_1353_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_rhsVarMask_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*4, v_perm_1354_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; 
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*4 + 1, v_fallback_1338_);
v___x_1362_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1359_, v___x_1361_, v_attrKind_1337_, v_a_1340_, v_a_1341_, v_a_1342_);
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1349_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1349_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_dec(v_declName_1336_);
return v___x_1348_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addHomoAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1336_ = stack[0].m_obj;
uint8_t v_attrKind_1337_ = stack[1].m_num;
uint8_t v_fallback_1338_ = stack[2].m_num;
lean_object* v_a_1339_ = stack[3].m_obj;
lean_object* v_a_1340_ = stack[4].m_obj;
lean_object* v_a_1341_ = stack[5].m_obj;
lean_object* v_a_1342_ = stack[6].m_obj;
lean_object* v_res_1373_;
v_res_1373_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_1336_, v_attrKind_1337_, v_fallback_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
stack->m_obj
 = v_res_1373_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object* v_declName_1374_, lean_object* v_attrKind_1375_, lean_object* v_fallback_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
uint8_t v_attrKind_boxed_1382_; uint8_t v_fallback_boxed_1383_; lean_object* v_res_1384_; 
v_attrKind_boxed_1382_ = lean_unbox(v_attrKind_1375_);
v_fallback_boxed_1383_ = lean_unbox(v_fallback_1376_);
v_res_1384_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_1374_, v_attrKind_boxed_1382_, v_fallback_boxed_1383_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
return v_res_1384_;
}
}
uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v_declName_1392_; lean_object* v_arity_1393_; lean_object* v_declName_1394_; lean_object* v_arity_1395_; uint8_t v___x_1396_; 
v_declName_1392_ = lean_ctor_get(v_x_1390_, 0);
v_arity_1393_ = lean_ctor_get(v_x_1390_, 1);
v_declName_1394_ = lean_ctor_get(v_x_1391_, 0);
v_arity_1395_ = lean_ctor_get(v_x_1391_, 1);
v___x_1396_ = lean_name_eq(v_declName_1392_, v_declName_1394_);
if (v___x_1396_ == 0)
{
return v___x_1396_;
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_nat_dec_eq(v_arity_1393_, v_arity_1395_);
return v___x_1397_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1390_ = stack[0].m_obj;
lean_object* v_x_1391_ = stack[1].m_obj;
uint8_t v_res_1398_;
v_res_1398_ = l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(v_x_1390_, v_x_1391_);
stack->m_num = v_res_1398_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(v_x_1399_, v_x_1400_);
lean_dec_ref(v_x_1400_);
lean_dec_ref(v_x_1399_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_s_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_fst_1407_ = lean_ctor_get(v_x_1406_, 0);
v_snd_1408_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1410_ = v_x_1406_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1407_);
lean_dec(v_x_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___y_1413_; lean_object* v___x_1418_; 
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_1405_, v_fst_1407_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_box(0);
v___y_1413_ = v___x_1419_;
goto v___jp_1412_;
}
else
{
lean_object* v_val_1420_; 
v_val_1420_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v___x_1418_, 1);
v___y_1413_ = v_val_1420_;
goto v___jp_1412_;
}
v___jp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 1);
lean_ctor_set(v___x_1410_, 1, v___y_1413_);
lean_ctor_set(v___x_1410_, 0, v_snd_1408_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_snd_1408_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___y_1413_);
v___x_1415_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1407_, v___x_1415_, v_s_1405_);
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_x_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_a_1423_);
lean_inc_ref_n(v___x_1424_, 2);
v___x_1425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_x_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(v_x_1426_, v_a_1427_);
lean_dec_ref(v_x_1426_);
return v_res_1428_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_));
v___x_1447_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1448_;
v_res_1448_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
return v_res_1450_;
}
}
lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_env_1455_; lean_object* v___x_1456_; lean_object* v_ext_1457_; lean_object* v_toEnvExtension_1458_; lean_object* v_asyncMode_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1453_ = lean_box(1);
v___x_1454_ = lean_st_ref_get(v_a_1451_);
v_env_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc_ref(v_env_1455_);
lean_dec(v___x_1454_);
v___x_1456_ = l_Lean_Meta_Grind_homoPredExt;
v_ext_1457_ = lean_ctor_get(v___x_1456_, 1);
v_toEnvExtension_1458_ = lean_ctor_get(v_ext_1457_, 0);
v_asyncMode_1459_ = lean_ctor_get(v_toEnvExtension_1458_, 2);
v___x_1460_ = 0;
v___x_1461_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1453_, v___x_1456_, v_env_1455_, v_asyncMode_1459_, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getHomoPredTheorems___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1451_ = stack[0].m_obj;
lean_object* v_res_1463_;
v_res_1463_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1451_);
stack->m_obj
 = v_res_1463_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1464_);
lean_dec(v_a_1464_);
return v_res_1466_;
}
}
lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getHomoPredTheorems_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1467_ = stack[0].m_obj;
lean_object* v_a_1468_ = stack[1].m_obj;
lean_object* v_res_1471_;
v_res_1471_ = l_Lean_Meta_Grind_getHomoPredTheorems(v_a_1467_, v_a_1468_);
stack->m_obj
 = v_res_1471_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_Grind_getHomoPredTheorems(v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
return v_res_1475_;
}
}
lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___f_1483_; lean_object* v___x_2163__overap_1484_; lean_object* v___x_1485_; 
v___f_1483_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0));
v___x_2163__overap_1484_ = lean_panic_fn_borrowed(v___f_1483_, v_msg_1477_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v___x_1485_ = lean_apply_5(v___x_2163__overap_1484_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, lean_box(0));
return v___x_1485_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1477_ = stack[0].m_obj;
lean_object* v___y_1478_ = stack[1].m_obj;
lean_object* v___y_1479_ = stack[2].m_obj;
lean_object* v___y_1480_ = stack[3].m_obj;
lean_object* v___y_1481_ = stack[4].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v_msg_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___boxed(lean_object* v_msg_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v_msg_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(lean_object* v_xs_1494_, lean_object* v_ys_1495_, lean_object* v_x_1496_){
_start:
{
lean_object* v_zero_1497_; uint8_t v_isZero_1498_; 
v_zero_1497_ = lean_unsigned_to_nat(0u);
v_isZero_1498_ = lean_nat_dec_eq(v_x_1496_, v_zero_1497_);
if (v_isZero_1498_ == 1)
{
lean_dec(v_x_1496_);
return v_isZero_1498_;
}
else
{
lean_object* v_one_1499_; lean_object* v_n_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v_one_1499_ = lean_unsigned_to_nat(1u);
v_n_1500_ = lean_nat_sub(v_x_1496_, v_one_1499_);
lean_dec(v_x_1496_);
v___x_1501_ = lean_array_fget_borrowed(v_xs_1494_, v_n_1500_);
v___x_1502_ = lean_array_fget_borrowed(v_ys_1495_, v_n_1500_);
v___x_1503_ = lean_expr_eqv(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec(v_n_1500_);
return v___x_1503_;
}
else
{
v_x_1496_ = v_n_1500_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1494_ = stack[0].m_obj;
lean_object* v_ys_1495_ = stack[1].m_obj;
lean_object* v_x_1496_ = stack[2].m_obj;
uint8_t v_res_1505_;
v_res_1505_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1494_, v_ys_1495_, v_x_1496_);
stack->m_num = v_res_1505_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg___boxed(lean_object* v_xs_1506_, lean_object* v_ys_1507_, lean_object* v_x_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1506_, v_ys_1507_, v_x_1508_);
lean_dec_ref(v_ys_1507_);
lean_dec_ref(v_xs_1506_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1511_; lean_object* v_dummy_1512_; 
v___x_1511_ = lean_box(0);
v_dummy_1512_ = l_Lean_Expr_sort___override(v___x_1511_);
return v_dummy_1512_;
}
}
uint8_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0(lean_object* v_a_1513_, lean_object* v_e_1514_){
_start:
{
uint8_t v___y_1516_; uint8_t v___x_1532_; 
v___x_1532_ = l_Lean_Expr_isApp(v_e_1514_);
if (v___x_1532_ == 0)
{
v___y_1516_ = v___x_1532_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = l_Lean_Expr_getAppFn(v_e_1514_);
v___x_1534_ = l_Lean_Expr_isConst(v___x_1533_);
lean_dec_ref(v___x_1533_);
v___y_1516_ = v___x_1534_;
goto v___jp_1515_;
}
v___jp_1515_:
{
if (v___y_1516_ == 0)
{
lean_dec_ref(v_e_1514_);
return v___y_1516_;
}
else
{
lean_object* v_dummy_1517_; lean_object* v_nargs_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_dummy_1517_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1518_ = l_Lean_Expr_getAppNumArgs(v_e_1514_);
lean_inc(v_nargs_1518_);
v___x_1519_ = lean_mk_array(v_nargs_1518_, v_dummy_1517_);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_sub(v_nargs_1518_, v___x_1520_);
lean_dec(v_nargs_1518_);
v___x_1522_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1514_, v___x_1519_, v___x_1521_);
v___x_1523_ = lean_array_get_size(v___x_1522_);
v___x_1524_ = lean_array_get_size(v_a_1513_);
v___x_1525_ = lean_nat_dec_lt(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1526_ = lean_nat_sub(v___x_1523_, v___x_1524_);
v___x_1527_ = l_Array_extract___redArg(v___x_1522_, v___x_1526_, v___x_1523_);
lean_dec_ref(v___x_1522_);
v___x_1528_ = lean_array_get_size(v___x_1527_);
v___x_1529_ = lean_nat_dec_eq(v___x_1528_, v___x_1524_);
if (v___x_1529_ == 0)
{
lean_dec_ref(v___x_1527_);
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v___x_1527_, v_a_1513_, v___x_1528_);
lean_dec_ref(v___x_1527_);
return v___x_1530_;
}
}
else
{
uint8_t v___x_1531_; 
lean_dec_ref(v___x_1522_);
v___x_1531_ = 0;
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addHomoPredAttr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1513_ = stack[0].m_obj;
lean_object* v_e_1514_ = stack[1].m_obj;
uint8_t v_res_1535_;
v_res_1535_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__0(v_a_1513_, v_e_1514_);
stack->m_num = v_res_1535_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed(lean_object* v_a_1536_, lean_object* v_e_1537_){
_start:
{
uint8_t v_res_1538_; lean_object* v_r_1539_; 
v_res_1538_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__0(v_a_1536_, v_e_1537_);
lean_dec_ref(v_a_1536_);
v_r_1539_ = lean_box(v_res_1538_);
return v_r_1539_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(lean_object* v_as_1540_, size_t v_i_1541_, size_t v_stop_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_a_1549_; uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_eq(v_i_1541_, v_stop_1542_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_array_uget_borrowed(v_as_1540_, v_i_1541_);
v___x_1555_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_1554_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___x_1557_; uint8_t v___x_1558_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = l_Lean_LocalDecl_binderInfo(v_a_1556_);
lean_dec(v_a_1556_);
v___x_1558_ = l_Lean_BinderInfo_isExplicit(v___x_1557_);
if (v___x_1558_ == 0)
{
v_a_1549_ = v_b_1543_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1559_; 
lean_inc(v___x_1554_);
v___x_1559_ = lean_array_push(v_b_1543_, v___x_1554_);
v_a_1549_ = v___x_1559_;
goto v___jp_1548_;
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_b_1543_);
v_a_1560_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1555_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1555_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_b_1543_);
return v___x_1568_;
}
v___jp_1548_:
{
size_t v___x_1550_; size_t v___x_1551_; 
v___x_1550_ = ((size_t)1ULL);
v___x_1551_ = lean_usize_add(v_i_1541_, v___x_1550_);
v_i_1541_ = v___x_1551_;
v_b_1543_ = v_a_1549_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1540_ = stack[0].m_obj;
size_t v_i_1541_ = stack[1].m_num;
size_t v_stop_1542_ = stack[2].m_num;
lean_object* v_b_1543_ = stack[3].m_obj;
lean_object* v___y_1544_ = stack[4].m_obj;
lean_object* v___y_1545_ = stack[5].m_obj;
lean_object* v___y_1546_ = stack[6].m_obj;
lean_object* v_res_1569_;
v_res_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1540_, v_i_1541_, v_stop_1542_, v_b_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
stack->m_obj
 = v_res_1569_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg___boxed(lean_object* v_as_1570_, lean_object* v_i_1571_, lean_object* v_stop_1572_, lean_object* v_b_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
size_t v_i_boxed_1578_; size_t v_stop_boxed_1579_; lean_object* v_res_1580_; 
v_i_boxed_1578_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_stop_boxed_1579_ = lean_unbox_usize(v_stop_1572_);
lean_dec(v_stop_1572_);
v_res_1580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1570_, v_i_boxed_1578_, v_stop_boxed_1579_, v_b_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec_ref(v_as_1570_);
return v_res_1580_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1584_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2));
v___x_1585_ = lean_unsigned_to_nat(41u);
v___x_1586_ = lean_unsigned_to_nat(169u);
v___x_1587_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1));
v___x_1588_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0));
v___x_1589_ = l_mkPanicMessageWithDecl(v___x_1588_, v___x_1587_, v___x_1586_, v___x_1585_, v___x_1584_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1(lean_object* v_declName_1604_, uint8_t v_attrKind_1605_, lean_object* v_xs_1606_, lean_object* v_type_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v_a_1635_; lean_object* v___y_1648_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_array_get_size(v_xs_1606_);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12));
v___x_1661_ = lean_nat_dec_lt(v___x_1658_, v___x_1659_);
if (v___x_1661_ == 0)
{
v_a_1635_ = v___x_1660_;
goto v___jp_1634_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v___x_1659_, v___x_1659_);
if (v___x_1662_ == 0)
{
if (v___x_1661_ == 0)
{
v_a_1635_ = v___x_1660_;
goto v___jp_1634_;
}
else
{
size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = ((size_t)0ULL);
v___x_1664_ = lean_usize_of_nat(v___x_1659_);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1606_, v___x_1663_, v___x_1664_, v___x_1660_, v___y_1608_, v___y_1610_, v___y_1611_);
v___y_1648_ = v___x_1665_;
goto v___jp_1647_;
}
}
else
{
size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = lean_usize_of_nat(v___x_1659_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1606_, v___x_1666_, v___x_1667_, v___x_1660_, v___y_1608_, v___y_1610_, v___y_1611_);
v___y_1648_ = v___x_1668_;
goto v___jp_1647_;
}
}
v___jp_1613_:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_find_expr(v___y_1614_, v_type_1607_);
lean_dec_ref(v___y_1614_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_val_1617_; lean_object* v___x_1618_; 
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l_Lean_Expr_getAppFn(v_val_1617_);
lean_dec(v_val_1617_);
if (lean_obj_tag(v___x_1618_) == 4)
{
lean_object* v_declName_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_declName_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_declName_1619_);
lean_dec_ref_known(v___x_1618_, 2);
v___x_1620_ = l_Lean_Meta_Grind_homoPredExt;
v___x_1621_ = lean_array_get_size(v___y_1615_);
lean_dec_ref(v___y_1615_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_declName_1604_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_declName_1619_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1620_, v___x_1623_, v_attrKind_1605_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec_ref(v___x_1618_);
lean_dec_ref(v___y_1615_);
lean_dec(v_declName_1604_);
v___x_1625_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3);
v___x_1626_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v___x_1625_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1626_;
}
}
else
{
lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v___x_1616_);
lean_dec_ref(v___y_1615_);
v___x_1627_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5);
v___x_1628_ = 0;
v___x_1629_ = l_Lean_MessageData_ofConstName(v_declName_1604_, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1627_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1632_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1633_;
}
}
v___jp_1634_:
{
lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
lean_inc_ref(v_a_1635_);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1636_, 0, v_a_1635_);
v___x_1637_ = lean_array_get_size(v_a_1635_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_nat_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
v___y_1614_ = v___f_1636_;
v___y_1615_ = v_a_1635_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec_ref(v___f_1636_);
lean_dec_ref(v_a_1635_);
v___x_1640_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1641_ = 0;
v___x_1642_ = l_Lean_MessageData_ofConstName(v_declName_1604_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1640_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1645_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1646_;
}
}
v___jp_1647_:
{
if (lean_obj_tag(v___y_1648_) == 0)
{
lean_object* v_a_1649_; 
v_a_1649_ = lean_ctor_get(v___y_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___y_1648_, 1);
v_a_1635_ = v_a_1649_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_declName_1604_);
v_a_1650_ = lean_ctor_get(v___y_1648_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___y_1648_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___y_1648_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___y_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addHomoPredAttr___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1604_ = stack[0].m_obj;
uint8_t v_attrKind_1605_ = stack[1].m_num;
lean_object* v_xs_1606_ = stack[2].m_obj;
lean_object* v_type_1607_ = stack[3].m_obj;
lean_object* v___y_1608_ = stack[4].m_obj;
lean_object* v___y_1609_ = stack[5].m_obj;
lean_object* v___y_1610_ = stack[6].m_obj;
lean_object* v___y_1611_ = stack[7].m_obj;
lean_object* v_res_1669_;
v_res_1669_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__1(v_declName_1604_, v_attrKind_1605_, v_xs_1606_, v_type_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
stack->m_obj
 = v_res_1669_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed(lean_object* v_declName_1670_, lean_object* v_attrKind_1671_, lean_object* v_xs_1672_, lean_object* v_type_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_attrKind_boxed_1679_; lean_object* v_res_1680_; 
v_attrKind_boxed_1679_ = lean_unbox(v_attrKind_1671_);
v_res_1680_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__1(v_declName_1670_, v_attrKind_boxed_1679_, v_xs_1672_, v_type_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v_type_1673_);
lean_dec_ref(v_xs_1672_);
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___closed__0));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object* v_declName_1684_, uint8_t v_attrKind_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(v_attrKind_1685_);
lean_inc_n(v_declName_1684_, 2);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1692_, 0, v_declName_1684_);
lean_closure_set(v___f_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1684_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___x_1703_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = l_Lean_ConstantInfo_type(v_a_1694_);
lean_dec(v_a_1694_);
lean_inc_ref(v___x_1695_);
v___x_1703_ = l_Lean_Meta_isProp(v___x_1695_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; uint8_t v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_unbox(v_a_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec_ref(v___x_1695_);
lean_dec_ref(v___f_1692_);
v___x_1706_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1707_ = lean_unbox(v_a_1704_);
lean_dec(v_a_1704_);
v___x_1708_ = l_Lean_MessageData_ofConstName(v_declName_1684_, v___x_1707_);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1706_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___closed__1, &l_Lean_Meta_Grind_addHomoPredAttr___closed__1_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1711_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
return v___x_1712_;
}
else
{
lean_dec(v_a_1704_);
lean_dec(v_declName_1684_);
v___y_1697_ = v_a_1686_;
v___y_1698_ = v_a_1687_;
v___y_1699_ = v_a_1688_;
v___y_1700_ = v_a_1689_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v___x_1695_);
lean_dec_ref(v___f_1692_);
lean_dec(v_declName_1684_);
v_a_1713_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1703_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1703_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
v___jp_1696_:
{
uint8_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = 0;
v___x_1702_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1695_, v___f_1692_, v___x_1701_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1702_;
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___f_1692_);
lean_dec(v_declName_1684_);
v_a_1721_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1693_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1693_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addHomoPredAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1684_ = stack[0].m_obj;
uint8_t v_attrKind_1685_ = stack[1].m_num;
lean_object* v_a_1686_ = stack[2].m_obj;
lean_object* v_a_1687_ = stack[3].m_obj;
lean_object* v_a_1688_ = stack[4].m_obj;
lean_object* v_a_1689_ = stack[5].m_obj;
lean_object* v_res_1729_;
v_res_1729_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_1684_, v_attrKind_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
stack->m_obj
 = v_res_1729_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___boxed(lean_object* v_declName_1730_, lean_object* v_attrKind_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
uint8_t v_attrKind_boxed_1737_; lean_object* v_res_1738_; 
v_attrKind_boxed_1737_ = lean_unbox(v_attrKind_1731_);
v_res_1738_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_1730_, v_attrKind_boxed_1737_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
return v_res_1738_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(lean_object* v_xs_1739_, lean_object* v_ys_1740_, lean_object* v_hsz_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1739_, v_ys_1740_, v_x_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1739_ = stack[0].m_obj;
lean_object* v_ys_1740_ = stack[1].m_obj;
lean_object* v_x_1742_ = stack[3].m_obj;
uint8_t v_res_1745_;
v_res_1745_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(v_xs_1739_, v_ys_1740_, lean_box(0), v_x_1742_, lean_box(0));
stack->m_num = v_res_1745_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___boxed(lean_object* v_xs_1746_, lean_object* v_ys_1747_, lean_object* v_hsz_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
uint8_t v_res_1751_; lean_object* v_r_1752_; 
v_res_1751_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(v_xs_1746_, v_ys_1747_, v_hsz_1748_, v_x_1749_, v_x_1750_);
lean_dec_ref(v_ys_1747_);
lean_dec_ref(v_xs_1746_);
v_r_1752_ = lean_box(v_res_1751_);
return v_r_1752_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(lean_object* v_as_1753_, size_t v_i_1754_, size_t v_stop_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1753_, v_i_1754_, v_stop_1755_, v_b_1756_, v___y_1757_, v___y_1759_, v___y_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1753_ = stack[0].m_obj;
size_t v_i_1754_ = stack[1].m_num;
size_t v_stop_1755_ = stack[2].m_num;
lean_object* v_b_1756_ = stack[3].m_obj;
lean_object* v___y_1757_ = stack[4].m_obj;
lean_object* v___y_1758_ = stack[5].m_obj;
lean_object* v___y_1759_ = stack[6].m_obj;
lean_object* v___y_1760_ = stack[7].m_obj;
lean_object* v_res_1763_;
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(v_as_1753_, v_i_1754_, v_stop_1755_, v_b_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
stack->m_obj
 = v_res_1763_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___boxed(lean_object* v_as_1764_, lean_object* v_i_1765_, lean_object* v_stop_1766_, lean_object* v_b_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
size_t v_i_boxed_1773_; size_t v_stop_boxed_1774_; lean_object* v_res_1775_; 
v_i_boxed_1773_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_stop_boxed_1774_ = lean_unbox_usize(v_stop_1766_);
lean_dec(v_stop_1766_);
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(v_as_1764_, v_i_boxed_1773_, v_stop_boxed_1774_, v_b_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec_ref(v_as_1764_);
return v_res_1775_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(lean_object* v___x_1776_, lean_object* v_as_x27_1777_, lean_object* v_b_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
if (lean_obj_tag(v_as_x27_1777_) == 0)
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_b_1778_);
return v___x_1784_;
}
else
{
lean_object* v_head_1785_; lean_object* v_tail_1786_; lean_object* v___y_1788_; uint8_t v___y_1789_; lean_object* v_a_1793_; lean_object* v_declName_1796_; lean_object* v_arity_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_head_1785_ = lean_ctor_get(v_as_x27_1777_, 0);
v_tail_1786_ = lean_ctor_get(v_as_x27_1777_, 1);
v_declName_1796_ = lean_ctor_get(v_head_1785_, 0);
v_arity_1797_ = lean_ctor_get(v_head_1785_, 1);
v___x_1798_ = lean_array_get_size(v___x_1776_);
v___x_1799_ = lean_nat_dec_le(v_arity_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
v_as_x27_1777_ = v_tail_1786_;
goto _start;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_nat_sub(v___x_1798_, v_arity_1797_);
v___x_1802_ = l_Array_extract___redArg(v___x_1776_, v___x_1801_, v___x_1798_);
lean_inc(v_declName_1796_);
v___x_1803_ = l_Lean_Meta_mkAppM(v_declName_1796_, v___x_1802_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc_n(v_a_1804_, 2);
lean_dec_ref_known(v___x_1803_, 1);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1779_);
v___x_1805_ = lean_infer_type(v_a_1804_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1804_);
lean_ctor_set(v___x_1807_, 1, v_a_1806_);
v___x_1808_ = lean_array_push(v_b_1778_, v___x_1807_);
v_as_x27_1777_ = v_tail_1786_;
v_b_1778_ = v___x_1808_;
goto _start;
}
else
{
lean_object* v_a_1810_; 
lean_dec(v_a_1804_);
v_a_1810_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1805_, 1);
v_a_1793_ = v_a_1810_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1811_; 
v_a_1811_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1803_, 1);
v_a_1793_ = v_a_1811_;
goto v___jp_1792_;
}
}
v___jp_1787_:
{
if (v___y_1789_ == 0)
{
lean_dec_ref(v___y_1788_);
v_as_x27_1777_ = v_tail_1786_;
goto _start;
}
else
{
lean_object* v___x_1791_; 
lean_dec_ref(v_b_1778_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___y_1788_);
return v___x_1791_;
}
}
v___jp_1792_:
{
uint8_t v___x_1794_; 
v___x_1794_ = l_Lean_Exception_isInterrupt(v_a_1793_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
lean_inc_ref(v_a_1793_);
v___x_1795_ = l_Lean_Exception_isRuntime(v_a_1793_);
v___y_1788_ = v_a_1793_;
v___y_1789_ = v___x_1795_;
goto v___jp_1787_;
}
else
{
v___y_1788_ = v_a_1793_;
v___y_1789_ = v___x_1794_;
goto v___jp_1787_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1776_ = stack[0].m_obj;
lean_object* v_as_x27_1777_ = stack[1].m_obj;
lean_object* v_b_1778_ = stack[2].m_obj;
lean_object* v___y_1779_ = stack[3].m_obj;
lean_object* v___y_1780_ = stack[4].m_obj;
lean_object* v___y_1781_ = stack[5].m_obj;
lean_object* v___y_1782_ = stack[6].m_obj;
lean_object* v_res_1812_;
v_res_1812_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1776_, v_as_x27_1777_, v_b_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
stack->m_obj
 = v_res_1812_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg___boxed(lean_object* v___x_1813_, lean_object* v_as_x27_1814_, lean_object* v_b_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1813_, v_as_x27_1814_, v_b_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v_as_x27_1814_);
lean_dec_ref(v___x_1813_);
return v_res_1821_;
}
}
lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object* v_e_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Expr_getAppFn(v_e_1824_);
if (lean_obj_tag(v___x_1830_) == 4)
{
lean_object* v_declName_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1851_; 
v_declName_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_declName_1831_);
lean_dec_ref_known(v___x_1830_, 2);
v___x_1832_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1828_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1851_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1851_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1833_, v_declName_1831_);
lean_dec(v_declName_1831_);
lean_dec(v_a_1833_);
if (lean_obj_tag(v___x_1837_) == 1)
{
lean_object* v_val_1838_; lean_object* v_dummy_1839_; lean_object* v_nargs_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_del_object(v___x_1835_);
v_val_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v_dummy_1839_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1840_ = l_Lean_Expr_getAppNumArgs(v_e_1824_);
lean_inc(v_nargs_1840_);
v___x_1841_ = lean_mk_array(v_nargs_1840_, v_dummy_1839_);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_nat_sub(v_nargs_1840_, v___x_1842_);
lean_dec(v_nargs_1840_);
v___x_1844_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1824_, v___x_1841_, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1846_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1844_, v_val_1838_, v___x_1845_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_val_1838_);
lean_dec_ref(v___x_1844_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec(v___x_1837_);
lean_dec_ref(v_e_1824_);
v___x_1847_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1847_);
v___x_1849_ = v___x_1835_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_e_1824_);
v___x_1852_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkHomoPredInstances_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1824_ = stack[0].m_obj;
lean_object* v_a_1825_ = stack[1].m_obj;
lean_object* v_a_1826_ = stack[2].m_obj;
lean_object* v_a_1827_ = stack[3].m_obj;
lean_object* v_a_1828_ = stack[4].m_obj;
lean_object* v_res_1854_;
v_res_1854_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___boxed(lean_object* v_e_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1861_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(lean_object* v___x_1862_, lean_object* v_as_1863_, lean_object* v_as_x27_1864_, lean_object* v_b_1865_, lean_object* v_a_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1862_, v_as_x27_1864_, v_b_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1862_ = stack[0].m_obj;
lean_object* v_as_1863_ = stack[1].m_obj;
lean_object* v_as_x27_1864_ = stack[2].m_obj;
lean_object* v_b_1865_ = stack[3].m_obj;
lean_object* v___y_1867_ = stack[5].m_obj;
lean_object* v___y_1868_ = stack[6].m_obj;
lean_object* v___y_1869_ = stack[7].m_obj;
lean_object* v___y_1870_ = stack[8].m_obj;
lean_object* v_res_1873_;
v_res_1873_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(v___x_1862_, v_as_1863_, v_as_x27_1864_, v_b_1865_, lean_box(0), v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
stack->m_obj
 = v_res_1873_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___boxed(lean_object* v___x_1874_, lean_object* v_as_1875_, lean_object* v_as_x27_1876_, lean_object* v_b_1877_, lean_object* v_a_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(v___x_1874_, v_as_1875_, v_as_x27_1876_, v_b_1877_, v_a_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v_as_x27_1876_);
lean_dec(v_as_1875_);
lean_dec_ref(v___x_1874_);
return v_res_1884_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_homoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_homoExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_homoSourceTypesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_homoSourceTypesExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_homoPredExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_homoPredExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
}
#ifdef __cplusplus
}
#endif
