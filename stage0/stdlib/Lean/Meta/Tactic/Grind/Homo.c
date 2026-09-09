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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpExt(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19;
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoPredExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Lean_Meta_Grind_homoExt;
v___x_18_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_17_, v_a_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg___boxed(lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_19_);
lean_dec(v_a_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems(lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___boxed(lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_getHomoTheorems(v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v_x_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v_a_31_);
lean_inc_ref_n(v___x_32_, 2);
v___x_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_x_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v_x_34_, v_a_35_);
lean_dec_ref(v_x_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v___y_37_){
_start:
{
lean_inc(v___y_37_);
return v___y_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v___y_38_);
lean_dec(v___y_38_);
return v_res_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___f_49_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___f_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_51_ = l_Lean_NameSet_empty;
v___f_52_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_54_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___f_52_);
lean_ctor_set(v___x_54_, 2, v___x_51_);
lean_ctor_set(v___x_54_, 3, v___f_50_);
lean_ctor_set(v___x_54_, 4, v___f_49_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_);
v___x_57_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_ext_65_; lean_object* v_toEnvExtension_66_; lean_object* v_asyncMode_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_62_ = lean_st_ref_get(v_a_60_);
v_env_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_env_63_);
lean_dec(v___x_62_);
v___x_64_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v_ext_65_ = lean_ctor_get(v___x_64_, 1);
v_toEnvExtension_66_ = lean_ctor_get(v_ext_65_, 0);
v_asyncMode_67_ = lean_ctor_get(v_toEnvExtension_66_, 2);
v___x_68_ = lean_box(1);
v___x_69_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_68_, v___x_64_, v_env_63_, v_asyncMode_67_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg___boxed(lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_71_);
lean_dec(v_a_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes(lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_Grind_getHomoSourceTypes(v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(lean_object* v_k_82_, lean_object* v_b_83_, lean_object* v_c_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
v___x_90_ = lean_apply_7(v_k_82_, v_b_83_, v_c_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, lean_box(0));
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed(lean_object* v_k_91_, lean_object* v_b_92_, lean_object* v_c_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(v_k_91_, v_b_92_, v_c_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(lean_object* v_type_100_, lean_object* v_k_101_, uint8_t v_cleanupAnnotations_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___f_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___f_108_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_108_, 0, v_k_101_);
v___x_109_ = 0;
v___x_110_ = lean_box(0);
v___x_111_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_109_, v___x_110_, v_type_100_, v___f_108_, v_cleanupAnnotations_102_, v___x_109_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_111_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_111_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___boxed(lean_object* v_type_128_, lean_object* v_k_129_, lean_object* v_cleanupAnnotations_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_136_; lean_object* v_res_137_; 
v_cleanupAnnotations_boxed_136_ = lean_unbox(v_cleanupAnnotations_130_);
v_res_137_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_128_, v_k_129_, v_cleanupAnnotations_boxed_136_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_object* v_00_u03b1_138_, lean_object* v_type_139_, lean_object* v_k_140_, uint8_t v_cleanupAnnotations_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_139_, v_k_140_, v_cleanupAnnotations_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___boxed(lean_object* v_00_u03b1_148_, lean_object* v_type_149_, lean_object* v_k_150_, lean_object* v_cleanupAnnotations_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_157_; lean_object* v_res_158_; 
v_cleanupAnnotations_boxed_157_ = lean_unbox(v_cleanupAnnotations_151_);
v_res_158_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(v_00_u03b1_148_, v_type_149_, v_k_150_, v_cleanupAnnotations_boxed_157_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_158_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(lean_object* v_k_159_, lean_object* v_t_160_){
_start:
{
if (lean_obj_tag(v_t_160_) == 0)
{
lean_object* v_k_161_; lean_object* v_l_162_; lean_object* v_r_163_; uint8_t v___x_164_; 
v_k_161_ = lean_ctor_get(v_t_160_, 1);
v_l_162_ = lean_ctor_get(v_t_160_, 3);
v_r_163_ = lean_ctor_get(v_t_160_, 4);
v___x_164_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_159_, v_k_161_);
switch(v___x_164_)
{
case 0:
{
v_t_160_ = v_l_162_;
goto _start;
}
case 1:
{
uint8_t v___x_166_; 
v___x_166_ = 1;
return v___x_166_;
}
default: 
{
v_t_160_ = v_r_163_;
goto _start;
}
}
}
else
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg___boxed(lean_object* v_k_169_, lean_object* v_t_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_169_, v_t_170_);
lean_dec(v_t_170_);
lean_dec(v_k_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_env_180_; lean_object* v___x_181_; lean_object* v_toCold_182_; lean_object* v_mctx_183_; lean_object* v_lctx_184_; lean_object* v_options_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_179_ = lean_st_ref_get(v___y_177_);
v_env_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref(v_env_180_);
lean_dec(v___x_179_);
v___x_181_ = lean_st_ref_get(v___y_175_);
v_toCold_182_ = lean_ctor_get(v___y_176_, 0);
v_mctx_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc_ref(v_mctx_183_);
lean_dec(v___x_181_);
v_lctx_184_ = lean_ctor_get(v___y_174_, 2);
v_options_185_ = lean_ctor_get(v_toCold_182_, 2);
lean_inc_ref(v_options_185_);
lean_inc_ref(v_lctx_184_);
v___x_186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_186_, 0, v_env_180_);
lean_ctor_set(v___x_186_, 1, v_mctx_183_);
lean_ctor_set(v___x_186_, 2, v_lctx_184_);
lean_ctor_set(v___x_186_, 3, v_options_185_);
v___x_187_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_msgData_173_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5___boxed(lean_object* v_msgData_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msgData_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_ref_202_ = lean_ctor_get(v___y_199_, 2);
v___x_203_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msg_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_inc(v_ref_202_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_ref_202_);
lean_ctor_set(v___x_208_, 1, v_a_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 1);
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg___boxed(lean_object* v_msg_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6));
v___x_231_ = l_Lean_stringToMessageData(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(lean_object* v___x_238_, lean_object* v_declName_239_, lean_object* v_as_240_, size_t v_sz_241_, size_t v_i_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_a_250_; uint8_t v___x_254_; 
v___x_254_ = lean_usize_dec_lt(v_i_242_, v_sz_241_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_declName_239_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_b_243_);
return v___x_255_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_257_; 
v_a_256_ = lean_array_uget_borrowed(v_as_240_, v_i_242_);
v___x_257_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_a_256_, v___y_244_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___x_259_ = lean_box(0);
v___x_260_ = l_Lean_LocalDecl_binderInfo(v_a_258_);
lean_dec(v_a_258_);
if (v___x_260_ == 3)
{
v_a_250_ = v___x_259_;
goto v___jp_249_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = l_Lean_Expr_fvarId_x21(v_a_256_);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_261_, v___x_238_);
lean_dec(v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v_a_256_);
v___x_263_ = lean_infer_type(v_a_256_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_n(v_a_264_, 2);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = l_Lean_Meta_isProp(v_a_264_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; uint8_t v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = lean_unbox(v_a_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_a_264_);
v___x_268_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1);
lean_inc(v_a_256_);
v___x_269_ = l_Lean_MessageData_ofExpr(v_a_256_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_unbox(v_a_266_);
lean_dec(v_a_266_);
lean_inc(v_declName_239_);
v___x_274_ = l_Lean_MessageData_ofConstName(v_declName_239_, v___x_273_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_272_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_277_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_dec_ref_known(v___x_278_, 1);
v_a_250_ = v___x_259_;
goto v___jp_249_;
}
else
{
lean_dec(v_declName_239_);
return v___x_278_;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_a_266_);
v___x_279_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7);
lean_inc(v_declName_239_);
v___x_280_ = l_Lean_MessageData_ofConstName(v_declName_239_, v___x_262_);
v___x_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l_Lean_indentExpr(v_a_264_);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_287_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_dec_ref_known(v___x_288_, 1);
v_a_250_ = v___x_259_;
goto v___jp_249_;
}
else
{
lean_dec(v_declName_239_);
return v___x_288_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_264_);
lean_dec(v_declName_239_);
v_a_289_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_265_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_265_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
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
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_declName_239_);
v_a_297_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_263_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_263_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
v_a_250_ = v___x_259_;
goto v___jp_249_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_declName_239_);
v_a_305_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_257_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_257_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
v___jp_249_:
{
size_t v___x_251_; size_t v___x_252_; 
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_242_, v___x_251_);
v_i_242_ = v___x_252_;
v_b_243_ = v_a_250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___boxed(lean_object* v___x_313_, lean_object* v_declName_314_, lean_object* v_as_315_, lean_object* v_sz_316_, lean_object* v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
size_t v_sz_boxed_324_; size_t v_i_boxed_325_; lean_object* v_res_326_; 
v_sz_boxed_324_ = lean_unbox_usize(v_sz_316_);
lean_dec(v_sz_316_);
v_i_boxed_325_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v___x_313_, v_declName_314_, v_as_315_, v_sz_boxed_324_, v_i_boxed_325_, v_b_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v_as_315_);
lean_dec(v___x_313_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(lean_object* v___x_327_, lean_object* v_as_328_, size_t v_sz_329_, size_t v_i_330_, lean_object* v_b_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_lt(v_i_330_, v_sz_329_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec(v___x_327_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_b_331_);
return v___x_338_;
}
else
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_array_uget_borrowed(v_as_328_, v_i_330_);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v_a_339_);
v___x_340_ = lean_infer_type(v_a_339_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_367_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_367_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_367_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_367_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_366_; 
v_fst_345_ = lean_ctor_get(v_b_331_, 0);
v_snd_346_ = lean_ctor_get(v_b_331_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_b_331_);
if (v_isSharedCheck_366_ == 0)
{
v___x_348_ = v_b_331_;
v_isShared_349_ = v_isSharedCheck_366_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snd_346_);
lean_inc(v_fst_345_);
lean_dec(v_b_331_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_366_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = l_Lean_Expr_fvarId_x21(v_a_339_);
v___x_358_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_357_, v_fst_345_);
lean_dec(v___x_357_);
if (v___x_358_ == 0)
{
lean_del_object(v___x_343_);
lean_dec(v_a_341_);
goto v___jp_350_;
}
else
{
uint8_t v___x_359_; 
v___x_359_ = l_Lean_Expr_containsFVar(v_a_341_, v___x_327_);
lean_dec(v_a_341_);
if (v___x_359_ == 0)
{
lean_del_object(v___x_343_);
goto v___jp_350_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
lean_del_object(v___x_348_);
lean_dec(v_snd_346_);
v___x_360_ = l_Lean_FVarIdSet_insert(v_fst_345_, v___x_327_);
v___x_361_ = lean_box(v___x_359_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_362_);
v___x_364_ = v___x_343_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
v___jp_350_:
{
lean_object* v___x_352_; 
if (v_isShared_349_ == 0)
{
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_fst_345_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_snd_346_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
size_t v___x_353_; size_t v___x_354_; 
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_330_, v___x_353_);
v_i_330_ = v___x_354_;
v_b_331_ = v___x_352_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_b_331_);
lean_dec(v___x_327_);
v_a_368_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_340_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_340_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1___boxed(lean_object* v___x_376_, lean_object* v_as_377_, lean_object* v_sz_378_, lean_object* v_i_379_, lean_object* v_b_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_378_);
lean_dec(v_sz_378_);
v_i_boxed_387_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_376_, v_as_377_, v_sz_boxed_386_, v_i_boxed_387_, v_b_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec_ref(v_as_377_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(lean_object* v_xs_389_, lean_object* v_as_390_, size_t v_sz_391_, size_t v_i_392_, lean_object* v_b_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_a_400_; uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_lt(v_i_392_, v_sz_391_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_b_393_);
return v___x_405_;
}
else
{
lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_433_; 
v_fst_406_ = lean_ctor_get(v_b_393_, 0);
v_snd_407_ = lean_ctor_get(v_b_393_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_b_393_);
if (v_isSharedCheck_433_ == 0)
{
v___x_409_ = v_b_393_;
v_isShared_410_ = v_isSharedCheck_433_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_snd_407_);
lean_inc(v_fst_406_);
lean_dec(v_b_393_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_433_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_a_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_a_411_ = lean_array_uget_borrowed(v_as_390_, v_i_392_);
v___x_412_ = l_Lean_Expr_fvarId_x21(v_a_411_);
v___x_413_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_412_, v_fst_406_);
if (v___x_413_ == 0)
{
lean_object* v___x_415_; 
if (v_isShared_410_ == 0)
{
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fst_406_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_snd_407_);
v___x_415_ = v_reuseFailAlloc_429_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
size_t v_sz_416_; size_t v___x_417_; lean_object* v___x_418_; 
v_sz_416_ = lean_array_size(v_xs_389_);
v___x_417_ = ((size_t)0ULL);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_412_, v_xs_389_, v_sz_416_, v___x_417_, v___x_415_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_fst_420_; lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v_fst_420_ = lean_ctor_get(v_a_419_, 0);
v_snd_421_ = lean_ctor_get(v_a_419_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v_a_419_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_inc(v_fst_420_);
lean_dec(v_a_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_snd_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
v_a_400_ = v___x_426_;
goto v___jp_399_;
}
}
}
else
{
return v___x_418_;
}
}
}
else
{
lean_object* v___x_431_; 
lean_dec(v___x_412_);
if (v_isShared_410_ == 0)
{
v___x_431_ = v___x_409_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_fst_406_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_snd_407_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v_a_400_ = v___x_431_;
goto v___jp_399_;
}
}
}
}
v___jp_399_:
{
size_t v___x_401_; size_t v___x_402_; 
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_add(v_i_392_, v___x_401_);
v_i_392_ = v___x_402_;
v_b_393_ = v_a_400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2___boxed(lean_object* v_xs_434_, lean_object* v_as_435_, lean_object* v_sz_436_, lean_object* v_i_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
size_t v_sz_boxed_444_; size_t v_i_boxed_445_; lean_object* v_res_446_; 
v_sz_boxed_444_ = lean_unbox_usize(v_sz_436_);
lean_dec(v_sz_436_);
v_i_boxed_445_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_434_, v_as_435_, v_sz_boxed_444_, v_i_boxed_445_, v_b_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v_as_435_);
lean_dec_ref(v_xs_434_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(lean_object* v_xs_447_, lean_object* v_a_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_snd_454_; uint8_t v___x_455_; 
v_snd_454_ = lean_ctor_get(v_a_448_, 1);
v___x_455_ = lean_unbox(v_snd_454_);
if (v___x_455_ == 0)
{
lean_object* v_fst_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_snd_454_);
v_fst_456_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_a_448_, 1);
lean_dec(v_unused_465_);
v___x_458_ = v_a_448_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_fst_456_);
lean_dec(v_a_448_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_snd_454_);
v___x_461_ = v_reuseFailAlloc_463_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
else
{
lean_object* v_fst_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_489_; 
v_fst_466_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_a_448_, 1);
lean_dec(v_unused_490_);
v___x_468_ = v_a_448_;
v_isShared_469_ = v_isSharedCheck_489_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_fst_466_);
lean_dec(v_a_448_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_489_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = 0;
v___x_471_ = lean_box(v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fst_466_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_488_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
size_t v_sz_474_; size_t v___x_475_; lean_object* v___x_476_; 
v_sz_474_ = lean_array_size(v_xs_447_);
v___x_475_ = ((size_t)0ULL);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_447_, v_xs_447_, v_sz_474_, v___x_475_, v___x_473_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v_fst_478_ = lean_ctor_get(v_a_477_, 0);
v_snd_479_ = lean_ctor_get(v_a_477_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v_a_477_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_inc(v_fst_478_);
lean_dec(v_a_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_fst_478_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_snd_479_);
v___x_484_ = v_reuseFailAlloc_486_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v_a_448_ = v___x_484_;
goto _start;
}
}
}
else
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg___boxed(lean_object* v_xs_491_, lean_object* v_a_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_491_, v_a_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec_ref(v_xs_491_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(lean_object* v___y_499_, lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_){
_start:
{
lean_object* v_a_506_; uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_b_503_);
return v___x_511_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_a_512_ = lean_array_uget_borrowed(v_as_500_, v_i_502_);
v___x_513_ = l_Lean_Expr_fvarId_x21(v_a_512_);
v___x_514_ = l_Lean_Expr_containsFVar(v___y_499_, v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v___x_513_);
v_a_506_ = v_b_503_;
goto v___jp_505_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_FVarIdSet_insert(v_b_503_, v___x_513_);
v_a_506_ = v___x_515_;
goto v___jp_505_;
}
}
v___jp_505_:
{
size_t v___x_507_; size_t v___x_508_; 
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_502_, v___x_507_);
v_i_502_ = v___x_508_;
v_b_503_ = v_a_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg___boxed(lean_object* v___y_516_, lean_object* v_as_517_, lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_b_520_, lean_object* v___y_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_523_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_516_, v_as_517_, v_sz_boxed_522_, v_i_boxed_523_, v_b_520_);
lean_dec_ref(v_as_517_);
lean_dec_ref(v___y_516_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0(lean_object* v___x_534_, lean_object* v_declName_535_, lean_object* v_xs_536_, lean_object* v_concl_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___x_545_; lean_object* v___y_547_; 
lean_inc_ref(v_concl_537_);
v___x_543_ = l_Lean_Expr_cleanupAnnotations(v_concl_537_);
v___x_544_ = l_Lean_Expr_isApp(v___x_543_);
v___x_545_ = 1;
if (v___x_544_ == 0)
{
lean_dec_ref(v___x_543_);
v___y_547_ = v_concl_537_;
goto v___jp_546_;
}
else
{
lean_object* v_arg_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_arg_583_ = lean_ctor_get(v___x_543_, 1);
lean_inc_ref(v_arg_583_);
v___x_584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_543_);
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1));
v___x_586_ = l_Lean_Expr_isConstOf(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
lean_dec_ref(v_arg_583_);
v___x_587_ = l_Lean_Expr_isApp(v___x_584_);
if (v___x_587_ == 0)
{
lean_dec_ref(v___x_584_);
v___y_547_ = v_concl_537_;
goto v___jp_546_;
}
else
{
lean_object* v_arg_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_arg_588_ = lean_ctor_get(v___x_584_, 1);
lean_inc_ref(v_arg_588_);
v___x_589_ = l_Lean_Expr_appFnCleanup___redArg(v___x_584_);
v___x_590_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_591_ = l_Lean_Expr_isConstOf(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; 
v___x_592_ = l_Lean_Expr_isApp(v___x_589_);
if (v___x_592_ == 0)
{
lean_dec_ref(v___x_589_);
lean_dec_ref(v_arg_588_);
v___y_547_ = v_concl_537_;
goto v___jp_546_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = l_Lean_Expr_appFnCleanup___redArg(v___x_589_);
v___x_594_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_595_ = l_Lean_Expr_isConstOf(v___x_593_, v___x_594_);
lean_dec_ref(v___x_593_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_arg_588_);
v___y_547_ = v_concl_537_;
goto v___jp_546_;
}
else
{
lean_dec_ref(v_concl_537_);
v___y_547_ = v_arg_588_;
goto v___jp_546_;
}
}
}
else
{
lean_dec_ref(v___x_589_);
lean_dec_ref(v_concl_537_);
v___y_547_ = v_arg_588_;
goto v___jp_546_;
}
}
}
else
{
lean_dec_ref(v___x_584_);
lean_dec_ref(v_concl_537_);
v___y_547_ = v_arg_583_;
goto v___jp_546_;
}
}
v___jp_546_:
{
size_t v_sz_548_; size_t v___x_549_; lean_object* v___x_550_; 
v_sz_548_ = lean_array_size(v_xs_536_);
v___x_549_ = ((size_t)0ULL);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_547_, v_xs_536_, v_sz_548_, v___x_549_, v___x_534_);
lean_dec_ref(v___y_547_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_box(v___x_545_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_a_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_536_, v___x_553_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v_fst_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v_fst_556_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_fst_556_);
lean_dec(v_a_555_);
v___x_557_ = lean_box(0);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v_fst_556_, v_declName_535_, v_xs_536_, v_sz_548_, v___x_549_, v___x_557_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v_fst_556_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_558_, 0);
lean_dec(v_unused_566_);
v___x_560_ = v___x_558_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_dec(v___x_558_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_557_);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_557_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
return v___x_558_;
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_declName_535_);
v_a_567_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_554_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_declName_535_);
v_a_575_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_550_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_550_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed(lean_object* v___x_596_, lean_object* v_declName_597_, lean_object* v_xs_598_, lean_object* v_concl_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Meta_Grind_validateHomoTheorem___lam__0(v___x_596_, v_declName_597_, v_xs_598_, v_concl_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v_xs_598_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(lean_object* v_ref_606_, lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_toCold_613_; lean_object* v_currRecDepth_614_; lean_object* v_ref_615_; uint8_t v_diag_616_; uint8_t v_suppressElabErrors_617_; lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_toCold_613_ = lean_ctor_get(v___y_610_, 0);
v_currRecDepth_614_ = lean_ctor_get(v___y_610_, 1);
v_ref_615_ = lean_ctor_get(v___y_610_, 2);
v_diag_616_ = lean_ctor_get_uint8(v___y_610_, sizeof(void*)*3);
v_suppressElabErrors_617_ = lean_ctor_get_uint8(v___y_610_, sizeof(void*)*3 + 1);
v_ref_618_ = l_Lean_replaceRef(v_ref_606_, v_ref_615_);
lean_inc(v_currRecDepth_614_);
lean_inc_ref(v_toCold_613_);
v___x_619_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_619_, 0, v_toCold_613_);
lean_ctor_set(v___x_619_, 1, v_currRecDepth_614_);
lean_ctor_set(v___x_619_, 2, v_ref_618_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3, v_diag_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 1, v_suppressElabErrors_617_);
v___x_620_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_607_, v___y_608_, v___y_609_, v___x_619_, v___y_611_);
lean_dec_ref_known(v___x_619_, 3);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg___boxed(lean_object* v_ref_621_, lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_621_, v_msg_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v_ref_621_);
return v_res_628_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_ctor_set(v___x_634_, 3, v___x_633_);
lean_ctor_set(v___x_634_, 4, v___x_632_);
lean_ctor_set(v___x_634_, 5, v___x_632_);
lean_ctor_set(v___x_634_, 6, v___x_632_);
lean_ctor_set(v___x_634_, 7, v___x_632_);
lean_ctor_set(v___x_634_, 8, v___x_632_);
lean_ctor_set(v___x_634_, 9, v___x_632_);
lean_ctor_set(v___x_634_, 10, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(32u);
v___x_636_ = lean_mk_empty_array_with_capacity(v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = ((size_t)5ULL);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_unsigned_to_nat(32u);
v___x_641_ = lean_mk_empty_array_with_capacity(v___x_640_);
v___x_642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_643_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
lean_ctor_set(v___x_643_, 2, v___x_639_);
lean_ctor_set(v___x_643_, 3, v___x_639_);
lean_ctor_set_usize(v___x_643_, 4, v___x_638_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_box(1);
v___x_645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_646_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
lean_ctor_set(v___x_647_, 2, v___x_644_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_669_, lean_object* v_declHint_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v_env_674_; uint8_t v___x_675_; 
v___x_673_ = lean_st_ref_get(v___y_671_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_env_674_);
lean_dec(v___x_673_);
v___x_675_ = l_Lean_Name_isAnonymous(v_declHint_670_);
if (v___x_675_ == 0)
{
uint8_t v_isExporting_676_; 
v_isExporting_676_ = lean_ctor_get_uint8(v_env_674_, sizeof(void*)*8);
if (v_isExporting_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec_ref(v_env_674_);
lean_dec(v_declHint_670_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_msg_669_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; uint8_t v___x_679_; 
lean_inc_ref(v_env_674_);
v___x_678_ = l_Lean_Environment_setExporting(v_env_674_, v___x_675_);
lean_inc(v_declHint_670_);
lean_inc_ref(v___x_678_);
v___x_679_ = l_Lean_Environment_contains(v___x_678_, v_declHint_670_, v_isExporting_676_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec_ref(v___x_678_);
lean_dec_ref(v_env_674_);
lean_dec(v_declHint_670_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_msg_669_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_c_686_; lean_object* v___x_687_; 
v___x_681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_683_ = l_Lean_Options_empty;
v___x_684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_684_, 0, v___x_678_);
lean_ctor_set(v___x_684_, 1, v___x_681_);
lean_ctor_set(v___x_684_, 2, v___x_682_);
lean_ctor_set(v___x_684_, 3, v___x_683_);
lean_inc(v_declHint_670_);
v___x_685_ = l_Lean_MessageData_ofConstName(v_declHint_670_, v___x_675_);
v_c_686_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_686_, 0, v___x_684_);
lean_ctor_set(v_c_686_, 1, v___x_685_);
v___x_687_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_674_, v_declHint_670_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v_env_674_);
lean_dec(v_declHint_670_);
v___x_688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_c_686_);
v___x_690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Lean_MessageData_note(v___x_691_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v_msg_669_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v_val_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_730_; 
v_val_695_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_730_ == 0)
{
v___x_697_ = v___x_687_;
v_isShared_698_ = v_isSharedCheck_730_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_val_695_);
lean_dec(v___x_687_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_730_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_mod_702_; uint8_t v___x_703_; 
v___x_699_ = lean_box(0);
v___x_700_ = l_Lean_Environment_header(v_env_674_);
lean_dec_ref(v_env_674_);
v___x_701_ = l_Lean_EnvironmentHeader_moduleNames(v___x_700_);
v_mod_702_ = lean_array_get(v___x_699_, v___x_701_, v_val_695_);
lean_dec(v_val_695_);
lean_dec_ref(v___x_701_);
v___x_703_ = l_Lean_isPrivateName(v_declHint_670_);
lean_dec(v_declHint_670_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_704_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_c_686_);
v___x_706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l_Lean_MessageData_ofName(v_mod_702_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = l_Lean_MessageData_note(v___x_711_);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v_msg_669_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 0);
lean_ctor_set(v___x_697_, 0, v___x_713_);
v___x_715_ = v___x_697_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_717_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_c_686_);
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_MessageData_ofName(v_mod_702_);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Lean_MessageData_note(v___x_724_);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v_msg_669_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 0);
lean_ctor_set(v___x_697_, 0, v___x_726_);
v___x_728_ = v___x_697_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_731_; 
lean_dec_ref(v_env_674_);
lean_dec(v_declHint_670_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v_msg_669_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_732_, lean_object* v_declHint_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_732_, v_declHint_733_, v___y_734_);
lean_dec(v___y_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_737_, lean_object* v_declHint_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_754_; 
v___x_744_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_737_, v_declHint_738_, v___y_742_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_754_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_749_ = l_Lean_unknownIdentifierMessageTag;
v___x_750_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_a_745_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_750_);
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_755_, lean_object* v_declHint_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_755_, v_declHint_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(lean_object* v_ref_763_, lean_object* v_msg_764_, lean_object* v_declHint_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; lean_object* v_a_772_; lean_object* v___x_773_; 
v___x_771_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_764_, v_declHint_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
v___x_773_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_763_, v_a_772_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_ref_774_, lean_object* v_msg_775_, lean_object* v_declHint_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_774_, v_msg_775_, v_declHint_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v_ref_774_);
return v_res_782_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_789_, lean_object* v_constName_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_796_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1);
v___x_797_ = 0;
lean_inc(v_constName_790_);
v___x_798_ = l_Lean_MessageData_ofConstName(v_constName_790_, v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_789_, v___x_801_, v_constName_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_803_, lean_object* v_constName_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_803_, v_constName_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_ref_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(lean_object* v_constName_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_ref_817_; lean_object* v___x_818_; 
v_ref_817_ = lean_ctor_get(v___y_814_, 2);
v___x_818_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_817_, v_constName_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg___boxed(lean_object* v_constName_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(lean_object* v_constName_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; lean_object* v_env_833_; uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_832_ = lean_st_ref_get(v___y_830_);
v_env_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_ref(v_env_833_);
lean_dec(v___x_832_);
v___x_834_ = 0;
lean_inc(v_constName_826_);
v___x_835_ = l_Lean_Environment_find_x3f(v_env_833_, v_constName_826_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v___x_836_;
}
else
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_constName_826_);
v_val_837_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_val_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7___boxed(lean_object* v_constName_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_constName_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem(lean_object* v_declName_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
lean_inc(v_declName_852_);
v___x_858_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_box(1);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed), 9, 2);
lean_closure_set(v___f_861_, 0, v___x_860_);
lean_closure_set(v___f_861_, 1, v_declName_852_);
v___x_862_ = l_Lean_ConstantInfo_type(v_a_859_);
lean_dec(v_a_859_);
v___x_863_ = 0;
v___x_864_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_862_, v___f_861_, v___x_863_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_864_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_declName_852_);
v_a_865_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_858_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_858_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object* v_declName_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_879_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_object* v_00_u03b2_880_, lean_object* v_k_881_, lean_object* v_t_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_881_, v_t_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___boxed(lean_object* v_00_u03b2_884_, lean_object* v_k_885_, lean_object* v_t_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(v_00_u03b2_884_, v_k_885_, v_t_886_);
lean_dec(v_t_886_);
lean_dec(v_k_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(lean_object* v___y_889_, lean_object* v_as_890_, size_t v_sz_891_, size_t v_i_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_889_, v_as_890_, v_sz_891_, v_i_892_, v_b_893_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___boxed(lean_object* v___y_900_, lean_object* v_as_901_, lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
size_t v_sz_boxed_910_; size_t v_i_boxed_911_; lean_object* v_res_912_; 
v_sz_boxed_910_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_911_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(v___y_900_, v_as_901_, v_sz_boxed_910_, v_i_boxed_911_, v_b_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec_ref(v_as_901_);
lean_dec_ref(v___y_900_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(lean_object* v_xs_913_, lean_object* v_inst_914_, lean_object* v_a_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_913_, v_a_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___boxed(lean_object* v_xs_922_, lean_object* v_inst_923_, lean_object* v_a_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(v_xs_922_, v_inst_923_, v_a_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_xs_922_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_object* v_00_u03b1_931_, lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___boxed(lean_object* v_00_u03b1_939_, lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(v_00_u03b1_939_, v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_object* v_00_u03b1_947_, lean_object* v_constName_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___boxed(lean_object* v_00_u03b1_955_, lean_object* v_constName_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(v_00_u03b1_955_, v_constName_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_963_, lean_object* v_ref_964_, lean_object* v_constName_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_964_, v_constName_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_972_, lean_object* v_ref_973_, lean_object* v_constName_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(v_00_u03b1_972_, v_ref_973_, v_constName_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v_ref_973_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_object* v_00_u03b1_981_, lean_object* v_ref_982_, lean_object* v_msg_983_, lean_object* v_declHint_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_982_, v_msg_983_, v_declHint_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___boxed(lean_object* v_00_u03b1_991_, lean_object* v_ref_992_, lean_object* v_msg_993_, lean_object* v_declHint_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(v_00_u03b1_991_, v_ref_992_, v_msg_993_, v_declHint_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v_ref_992_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(lean_object* v_msg_1001_, lean_object* v_declHint_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_1001_, v_declHint_1002_, v___y_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1009_, lean_object* v_declHint_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(v_msg_1009_, v_declHint_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_object* v_00_u03b1_1017_, lean_object* v_ref_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_1018_, v_msg_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_ref_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(v_00_u03b1_1026_, v_ref_1027_, v_msg_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v_ref_1027_);
return v_res_1034_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(lean_object* v_declName_1044_, lean_object* v_x_1045_, lean_object* v_concl_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___y_1056_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
lean_inc_ref(v_concl_1046_);
v___x_1082_ = l_Lean_Expr_cleanupAnnotations(v_concl_1046_);
v___x_1083_ = l_Lean_Expr_isApp(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v___x_1082_);
v___y_1056_ = v_concl_1046_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1082_);
v___x_1085_ = l_Lean_Expr_isApp(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v___x_1084_);
v___y_1056_ = v_concl_1046_;
goto v___jp_1055_;
}
else
{
lean_object* v_arg_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_arg_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc_ref(v_arg_1086_);
v___x_1087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1084_);
v___x_1088_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_1089_ = l_Lean_Expr_isConstOf(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Lean_Expr_isApp(v___x_1087_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v___x_1087_);
lean_dec_ref(v_arg_1086_);
v___y_1056_ = v_concl_1046_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1087_);
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1093_ = l_Lean_Expr_isConstOf(v___x_1091_, v___x_1092_);
lean_dec_ref(v___x_1091_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v_arg_1086_);
v___y_1056_ = v_concl_1046_;
goto v___jp_1055_;
}
else
{
lean_dec_ref(v_concl_1046_);
v___y_1056_ = v_arg_1086_;
goto v___jp_1055_;
}
}
}
else
{
lean_dec_ref(v___x_1087_);
lean_dec_ref(v_concl_1046_);
v___y_1056_ = v_arg_1086_;
goto v___jp_1055_;
}
}
}
v___jp_1052_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
v___jp_1055_:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = l_Lean_Expr_cleanupAnnotations(v___y_1056_);
v___x_1058_ = l_Lean_Expr_isApp(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v___x_1057_);
lean_dec(v_declName_1044_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1057_);
v___x_1060_ = l_Lean_Expr_isApp(v___x_1059_);
if (v___x_1060_ == 0)
{
lean_dec_ref(v___x_1059_);
lean_dec(v_declName_1044_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1059_);
v___x_1062_ = l_Lean_Expr_isApp(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v___x_1061_);
lean_dec(v_declName_1044_);
goto v___jp_1052_;
}
else
{
lean_object* v_arg_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_arg_1063_ = lean_ctor_get(v___x_1061_, 1);
lean_inc_ref(v_arg_1063_);
v___x_1064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1061_);
v___x_1065_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1066_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1065_);
lean_dec_ref(v___x_1064_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v_arg_1063_);
lean_dec(v_declName_1044_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Expr_getAppFn(v_arg_1063_);
if (lean_obj_tag(v___x_1067_) == 4)
{
lean_object* v_declName_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec_ref(v_arg_1063_);
lean_dec(v_declName_1044_);
v_declName_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_declName_1068_);
lean_dec_ref_known(v___x_1067_, 2);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_declName_1068_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___x_1067_);
v___x_1071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1);
v___x_1072_ = 0;
v___x_1073_ = l_Lean_MessageData_ofConstName(v_declName_1044_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1071_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_indentExpr(v_arg_1063_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1080_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1081_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed(lean_object* v_declName_1094_, lean_object* v_x_1095_, lean_object* v_concl_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(v_declName_1094_, v_x_1095_, v_concl_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v_x_1095_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(lean_object* v_declName_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
lean_inc(v_declName_1103_);
v___x_1109_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___f_1111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1111_, 0, v_declName_1103_);
v___x_1112_ = l_Lean_ConstantInfo_type(v_a_1110_);
lean_dec(v_a_1110_);
v___x_1113_ = 0;
v___x_1114_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1112_, v___f_1111_, v___x_1113_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1114_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_declName_1103_);
v_a_1115_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1109_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1109_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___boxed(lean_object* v_declName_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1);
v___x_1136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1135_);
lean_ctor_set(v___x_1136_, 3, v___x_1135_);
lean_ctor_set(v___x_1136_, 4, v___x_1135_);
lean_ctor_set(v___x_1136_, 5, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object* v_ext_1137_, lean_object* v_b_1138_, uint8_t v_kind_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_toCold_1144_; lean_object* v_currNamespace_1145_; lean_object* v___x_1146_; lean_object* v_env_1147_; lean_object* v_nextMacroScope_1148_; lean_object* v_ngen_1149_; lean_object* v_auxDeclNGen_1150_; lean_object* v_traceState_1151_; lean_object* v_messages_1152_; lean_object* v_infoState_1153_; lean_object* v_snapshotTasks_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1181_; 
v_toCold_1144_ = lean_ctor_get(v___y_1141_, 0);
v_currNamespace_1145_ = lean_ctor_get(v_toCold_1144_, 4);
v___x_1146_ = lean_st_ref_take(v___y_1142_);
v_env_1147_ = lean_ctor_get(v___x_1146_, 0);
v_nextMacroScope_1148_ = lean_ctor_get(v___x_1146_, 1);
v_ngen_1149_ = lean_ctor_get(v___x_1146_, 2);
v_auxDeclNGen_1150_ = lean_ctor_get(v___x_1146_, 3);
v_traceState_1151_ = lean_ctor_get(v___x_1146_, 4);
v_messages_1152_ = lean_ctor_get(v___x_1146_, 6);
v_infoState_1153_ = lean_ctor_get(v___x_1146_, 7);
v_snapshotTasks_1154_ = lean_ctor_get(v___x_1146_, 8);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v___x_1146_, 5);
lean_dec(v_unused_1182_);
v___x_1156_ = v___x_1146_;
v_isShared_1157_ = v_isSharedCheck_1181_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snapshotTasks_1154_);
lean_inc(v_infoState_1153_);
lean_inc(v_messages_1152_);
lean_inc(v_traceState_1151_);
lean_inc(v_auxDeclNGen_1150_);
lean_inc(v_ngen_1149_);
lean_inc(v_nextMacroScope_1148_);
lean_inc(v_env_1147_);
lean_dec(v___x_1146_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1181_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_inc(v_currNamespace_1145_);
v___x_1158_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1147_, v_ext_1137_, v_b_1138_, v_kind_1139_, v_currNamespace_1145_);
v___x_1159_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 5, v___x_1159_);
lean_ctor_set(v___x_1156_, 0, v___x_1158_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_nextMacroScope_1148_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_ngen_1149_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_auxDeclNGen_1150_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_traceState_1151_);
lean_ctor_set(v_reuseFailAlloc_1180_, 5, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1180_, 6, v_messages_1152_);
lean_ctor_set(v_reuseFailAlloc_1180_, 7, v_infoState_1153_);
lean_ctor_set(v_reuseFailAlloc_1180_, 8, v_snapshotTasks_1154_);
v___x_1161_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_mctx_1164_; lean_object* v_zetaDeltaFVarIds_1165_; lean_object* v_postponed_1166_; lean_object* v_diag_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1178_; 
v___x_1162_ = lean_st_ref_put(v___y_1142_, v___x_1161_);
v___x_1163_ = lean_st_ref_take(v___y_1140_);
v_mctx_1164_ = lean_ctor_get(v___x_1163_, 0);
v_zetaDeltaFVarIds_1165_ = lean_ctor_get(v___x_1163_, 2);
v_postponed_1166_ = lean_ctor_get(v___x_1163_, 3);
v_diag_1167_ = lean_ctor_get(v___x_1163_, 4);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v___x_1163_, 1);
lean_dec(v_unused_1179_);
v___x_1169_ = v___x_1163_;
v_isShared_1170_ = v_isSharedCheck_1178_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_diag_1167_);
lean_inc(v_postponed_1166_);
lean_inc(v_zetaDeltaFVarIds_1165_);
lean_inc(v_mctx_1164_);
lean_dec(v___x_1163_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1178_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_mctx_1164_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_zetaDeltaFVarIds_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_postponed_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_diag_1167_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_st_ref_put(v___y_1140_, v___x_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object* v_ext_1183_, lean_object* v_b_1184_, lean_object* v_kind_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_kind_boxed_1190_; lean_object* v_res_1191_; 
v_kind_boxed_1190_ = lean_unbox(v_kind_1185_);
v_res_1191_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1183_, v_b_1184_, v_kind_boxed_1190_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object* v_00_u03b1_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_00_u03c3_1194_, lean_object* v_ext_1195_, lean_object* v_b_1196_, uint8_t v_kind_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1195_, v_b_1196_, v_kind_1197_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_00_u03c3_1206_, lean_object* v_ext_1207_, lean_object* v_b_1208_, lean_object* v_kind_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v_kind_boxed_1215_; lean_object* v_res_1216_; 
v_kind_boxed_1215_ = lean_unbox(v_kind_1209_);
v_res_1216_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(v_00_u03b1_1204_, v_00_u03b2_1205_, v_00_u03c3_1206_, v_ext_1207_, v_b_1208_, v_kind_boxed_1215_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t v_attrKind_1217_, lean_object* v_declName_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
lean_inc(v_declName_1218_);
v___x_1224_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref_known(v___x_1224_, 1);
v___x_1225_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1237_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1237_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1237_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
if (lean_obj_tag(v_a_1226_) == 1)
{
lean_object* v_val_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_del_object(v___x_1228_);
v_val_1230_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v_a_1226_, 1);
v___x_1231_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v___x_1232_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1231_, v_val_1230_, v_attrKind_1217_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
lean_dec(v_a_1226_);
v___x_1233_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1233_);
v___x_1235_ = v___x_1228_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1225_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1225_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_dec(v_declName_1218_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object* v_attrKind_1246_, lean_object* v_declName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v_attrKind_boxed_1253_; lean_object* v_res_1254_; 
v_attrKind_boxed_1253_ = lean_unbox(v_attrKind_1246_);
v_res_1254_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_boxed_1253_, v_declName_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object* v_declName_1255_, uint8_t v_attrKind_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_box(v_attrKind_1256_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1263_, 0, v___x_1262_);
v___x_1264_ = l_Lean_Meta_Grind_homoExt;
v___x_1265_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v___x_1264_, v_declName_1255_, v_attrKind_1256_, v___f_1263_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object* v_declName_1266_, lean_object* v_attrKind_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
uint8_t v_attrKind_boxed_1273_; lean_object* v_res_1274_; 
v_attrKind_boxed_1273_ = lean_unbox(v_attrKind_1267_);
v_res_1274_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_1266_, v_attrKind_boxed_1273_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v_declName_1282_; lean_object* v_arity_1283_; lean_object* v_declName_1284_; lean_object* v_arity_1285_; uint8_t v___x_1286_; 
v_declName_1282_ = lean_ctor_get(v_x_1280_, 0);
v_arity_1283_ = lean_ctor_get(v_x_1280_, 1);
v_declName_1284_ = lean_ctor_get(v_x_1281_, 0);
v_arity_1285_ = lean_ctor_get(v_x_1281_, 1);
v___x_1286_ = lean_name_eq(v_declName_1282_, v_declName_1284_);
if (v___x_1286_ == 0)
{
return v___x_1286_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_eq(v_arity_1283_, v_arity_1285_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_res_1290_ = l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(v_x_1288_, v_x_1289_);
lean_dec_ref(v_x_1289_);
lean_dec_ref(v_x_1288_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_s_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v_fst_1296_; lean_object* v_snd_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1310_; 
v_fst_1296_ = lean_ctor_get(v_x_1295_, 0);
v_snd_1297_ = lean_ctor_get(v_x_1295_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_x_1295_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1299_ = v_x_1295_;
v_isShared_1300_ = v_isSharedCheck_1310_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_snd_1297_);
lean_inc(v_fst_1296_);
lean_dec(v_x_1295_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1310_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___y_1302_; lean_object* v___x_1307_; 
v___x_1307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_1294_, v_fst_1296_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_box(0);
v___y_1302_ = v___x_1308_;
goto v___jp_1301_;
}
else
{
lean_object* v_val_1309_; 
v_val_1309_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v___x_1307_, 1);
v___y_1302_ = v_val_1309_;
goto v___jp_1301_;
}
v___jp_1301_:
{
lean_object* v___x_1304_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 1, v___y_1302_);
lean_ctor_set(v___x_1299_, 0, v_snd_1297_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_snd_1297_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___y_1302_);
v___x_1304_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1296_, v___x_1304_, v_s_1294_);
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_x_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1312_);
lean_inc_ref_n(v___x_1313_, 2);
v___x_1314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_ctor_set(v___x_1314_, 2, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_x_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(v_x_1315_, v_a_1316_);
lean_dec_ref(v_x_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_));
v___x_1334_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1339_; lean_object* v_env_1340_; lean_object* v___x_1341_; lean_object* v_ext_1342_; lean_object* v_toEnvExtension_1343_; lean_object* v_asyncMode_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1339_ = lean_st_ref_get(v_a_1337_);
v_env_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_env_1340_);
lean_dec(v___x_1339_);
v___x_1341_ = l_Lean_Meta_Grind_homoPredExt;
v_ext_1342_ = lean_ctor_get(v___x_1341_, 1);
v_toEnvExtension_1343_ = lean_ctor_get(v_ext_1342_, 0);
v_asyncMode_1344_ = lean_ctor_get(v_toEnvExtension_1343_, 2);
v___x_1345_ = lean_box(1);
v___x_1346_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1345_, v___x_1341_, v_env_1340_, v_asyncMode_1344_);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1348_);
lean_dec(v_a_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Meta_Grind_getHomoPredTheorems(v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(lean_object* v_msg_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___f_1366_; lean_object* v___x_2163__overap_1367_; lean_object* v___x_1368_; 
v___f_1366_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0));
v___x_2163__overap_1367_ = lean_panic_fn_borrowed(v___f_1366_, v_msg_1360_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
v___x_1368_ = lean_apply_5(v___x_2163__overap_1367_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, lean_box(0));
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___boxed(lean_object* v_msg_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v_msg_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(lean_object* v_xs_1376_, lean_object* v_ys_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v_zero_1379_; uint8_t v_isZero_1380_; 
v_zero_1379_ = lean_unsigned_to_nat(0u);
v_isZero_1380_ = lean_nat_dec_eq(v_x_1378_, v_zero_1379_);
if (v_isZero_1380_ == 1)
{
lean_dec(v_x_1378_);
return v_isZero_1380_;
}
else
{
lean_object* v_one_1381_; lean_object* v_n_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_one_1381_ = lean_unsigned_to_nat(1u);
v_n_1382_ = lean_nat_sub(v_x_1378_, v_one_1381_);
lean_dec(v_x_1378_);
v___x_1383_ = lean_array_fget_borrowed(v_xs_1376_, v_n_1382_);
v___x_1384_ = lean_array_fget_borrowed(v_ys_1377_, v_n_1382_);
v___x_1385_ = lean_expr_eqv(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec(v_n_1382_);
return v___x_1385_;
}
else
{
v_x_1378_ = v_n_1382_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg___boxed(lean_object* v_xs_1387_, lean_object* v_ys_1388_, lean_object* v_x_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1387_, v_ys_1388_, v_x_1389_);
lean_dec_ref(v_ys_1388_);
lean_dec_ref(v_xs_1387_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1392_; lean_object* v_dummy_1393_; 
v___x_1392_ = lean_box(0);
v_dummy_1393_ = l_Lean_Expr_sort___override(v___x_1392_);
return v_dummy_1393_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0(lean_object* v_a_1394_, lean_object* v_e_1395_){
_start:
{
uint8_t v___y_1397_; uint8_t v___x_1413_; 
v___x_1413_ = l_Lean_Expr_isApp(v_e_1395_);
if (v___x_1413_ == 0)
{
v___y_1397_ = v___x_1413_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = l_Lean_Expr_getAppFn(v_e_1395_);
v___x_1415_ = l_Lean_Expr_isConst(v___x_1414_);
lean_dec_ref(v___x_1414_);
v___y_1397_ = v___x_1415_;
goto v___jp_1396_;
}
v___jp_1396_:
{
if (v___y_1397_ == 0)
{
lean_dec_ref(v_e_1395_);
return v___y_1397_;
}
else
{
lean_object* v_dummy_1398_; lean_object* v_nargs_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_dummy_1398_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1399_ = l_Lean_Expr_getAppNumArgs(v_e_1395_);
lean_inc(v_nargs_1399_);
v___x_1400_ = lean_mk_array(v_nargs_1399_, v_dummy_1398_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_sub(v_nargs_1399_, v___x_1401_);
lean_dec(v_nargs_1399_);
v___x_1403_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1395_, v___x_1400_, v___x_1402_);
v___x_1404_ = lean_array_get_size(v___x_1403_);
v___x_1405_ = lean_array_get_size(v_a_1394_);
v___x_1406_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = lean_nat_sub(v___x_1404_, v___x_1405_);
v___x_1408_ = l_Array_extract___redArg(v___x_1403_, v___x_1407_, v___x_1404_);
lean_dec_ref(v___x_1403_);
v___x_1409_ = lean_array_get_size(v___x_1408_);
v___x_1410_ = lean_nat_dec_eq(v___x_1409_, v___x_1405_);
if (v___x_1410_ == 0)
{
lean_dec_ref(v___x_1408_);
return v___x_1410_;
}
else
{
uint8_t v___x_1411_; 
v___x_1411_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v___x_1408_, v_a_1394_, v___x_1409_);
lean_dec_ref(v___x_1408_);
return v___x_1411_;
}
}
else
{
uint8_t v___x_1412_; 
lean_dec_ref(v___x_1403_);
v___x_1412_ = 0;
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed(lean_object* v_a_1416_, lean_object* v_e_1417_){
_start:
{
uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_res_1418_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__0(v_a_1416_, v_e_1417_);
lean_dec_ref(v_a_1416_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(lean_object* v_as_1420_, size_t v_i_1421_, size_t v_stop_1422_, lean_object* v_b_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_eq(v_i_1421_, v_stop_1422_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_array_uget_borrowed(v_as_1420_, v_i_1421_);
v___x_1430_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_1429_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_a_1433_; uint8_t v___x_1437_; uint8_t v___x_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1437_ = l_Lean_LocalDecl_binderInfo(v_a_1431_);
lean_dec(v_a_1431_);
v___x_1438_ = l_Lean_BinderInfo_isExplicit(v___x_1437_);
if (v___x_1438_ == 0)
{
v_a_1433_ = v_b_1423_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1439_; 
lean_inc(v___x_1429_);
v___x_1439_ = lean_array_push(v_b_1423_, v___x_1429_);
v_a_1433_ = v___x_1439_;
goto v___jp_1432_;
}
v___jp_1432_:
{
size_t v___x_1434_; size_t v___x_1435_; 
v___x_1434_ = ((size_t)1ULL);
v___x_1435_ = lean_usize_add(v_i_1421_, v___x_1434_);
v_i_1421_ = v___x_1435_;
v_b_1423_ = v_a_1433_;
goto _start;
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v_b_1423_);
v_a_1440_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1430_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1430_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1423_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg___boxed(lean_object* v_as_1449_, lean_object* v_i_1450_, lean_object* v_stop_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
size_t v_i_boxed_1457_; size_t v_stop_boxed_1458_; lean_object* v_res_1459_; 
v_i_boxed_1457_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_stop_boxed_1458_ = lean_unbox_usize(v_stop_1451_);
lean_dec(v_stop_1451_);
v_res_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1449_, v_i_boxed_1457_, v_stop_boxed_1458_, v_b_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_as_1449_);
return v_res_1459_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1463_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2));
v___x_1464_ = lean_unsigned_to_nat(41u);
v___x_1465_ = lean_unsigned_to_nat(163u);
v___x_1466_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1));
v___x_1467_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0));
v___x_1468_ = l_mkPanicMessageWithDecl(v___x_1467_, v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1(lean_object* v_declName_1483_, uint8_t v_attrKind_1484_, lean_object* v_xs_1485_, lean_object* v_type_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v_a_1514_; lean_object* v___y_1527_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_array_get_size(v_xs_1485_);
v___x_1539_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12));
v___x_1540_ = lean_nat_dec_lt(v___x_1537_, v___x_1538_);
if (v___x_1540_ == 0)
{
v_a_1514_ = v___x_1539_;
goto v___jp_1513_;
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_nat_dec_le(v___x_1538_, v___x_1538_);
if (v___x_1541_ == 0)
{
if (v___x_1540_ == 0)
{
v_a_1514_ = v___x_1539_;
goto v___jp_1513_;
}
else
{
size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = lean_usize_of_nat(v___x_1538_);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1485_, v___x_1542_, v___x_1543_, v___x_1539_, v___y_1487_, v___y_1489_, v___y_1490_);
v___y_1527_ = v___x_1544_;
goto v___jp_1526_;
}
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1538_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1485_, v___x_1545_, v___x_1546_, v___x_1539_, v___y_1487_, v___y_1489_, v___y_1490_);
v___y_1527_ = v___x_1547_;
goto v___jp_1526_;
}
}
v___jp_1492_:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_find_expr(v___y_1493_, v_type_1486_);
lean_dec_ref(v___y_1493_);
if (lean_obj_tag(v___x_1495_) == 1)
{
lean_object* v_val_1496_; lean_object* v___x_1497_; 
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = l_Lean_Expr_getAppFn(v_val_1496_);
lean_dec(v_val_1496_);
if (lean_obj_tag(v___x_1497_) == 4)
{
lean_object* v_declName_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_declName_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_declName_1498_);
lean_dec_ref_known(v___x_1497_, 2);
v___x_1499_ = l_Lean_Meta_Grind_homoPredExt;
v___x_1500_ = lean_array_get_size(v___y_1494_);
lean_dec_ref(v___y_1494_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_declName_1483_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_declName_1498_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1499_, v___x_1502_, v_attrKind_1484_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v___x_1497_);
lean_dec_ref(v___y_1494_);
lean_dec(v_declName_1483_);
v___x_1504_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3);
v___x_1505_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v___x_1504_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1505_;
}
}
else
{
lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1495_);
lean_dec_ref(v___y_1494_);
v___x_1506_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5);
v___x_1507_ = 0;
v___x_1508_ = l_Lean_MessageData_ofConstName(v_declName_1483_, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1511_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1512_;
}
}
v___jp_1513_:
{
lean_object* v___f_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
lean_inc_ref(v_a_1514_);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1515_, 0, v_a_1514_);
v___x_1516_ = lean_array_get_size(v_a_1514_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_nat_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
v___y_1493_ = v___f_1515_;
v___y_1494_ = v_a_1514_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v___f_1515_);
lean_dec_ref(v_a_1514_);
v___x_1519_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1520_ = 0;
v___x_1521_ = l_Lean_MessageData_ofConstName(v_declName_1483_, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1524_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1525_;
}
}
v___jp_1526_:
{
if (lean_obj_tag(v___y_1527_) == 0)
{
lean_object* v_a_1528_; 
v_a_1528_ = lean_ctor_get(v___y_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___y_1527_, 1);
v_a_1514_ = v_a_1528_;
goto v___jp_1513_;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_declName_1483_);
v_a_1529_ = lean_ctor_get(v___y_1527_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___y_1527_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___y_1527_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___y_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed(lean_object* v_declName_1548_, lean_object* v_attrKind_1549_, lean_object* v_xs_1550_, lean_object* v_type_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v_attrKind_boxed_1557_; lean_object* v_res_1558_; 
v_attrKind_boxed_1557_ = lean_unbox(v_attrKind_1549_);
v_res_1558_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__1(v_declName_1548_, v_attrKind_boxed_1557_, v_xs_1550_, v_type_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec_ref(v_type_1551_);
lean_dec_ref(v_xs_1550_);
return v_res_1558_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___closed__0));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object* v_declName_1562_, uint8_t v_attrKind_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; 
lean_inc(v_declName_1562_);
v___x_1569_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1562_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_ConstantInfo_type(v_a_1570_);
lean_dec(v_a_1570_);
lean_inc_ref(v___x_1571_);
v___x_1572_ = l_Lean_Meta_isProp(v___x_1571_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; uint8_t v___x_1583_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = lean_box(v_attrKind_1563_);
lean_inc(v_declName_1562_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1575_, 0, v_declName_1562_);
lean_closure_set(v___f_1575_, 1, v___x_1574_);
v___x_1583_ = lean_unbox(v_a_1573_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v___f_1575_);
lean_dec_ref(v___x_1571_);
v___x_1584_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1585_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
v___x_1586_ = l_Lean_MessageData_ofConstName(v_declName_1562_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1584_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___closed__1, &l_Lean_Meta_Grind_addHomoPredAttr___closed__1_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1589_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1590_;
}
else
{
lean_dec(v_a_1573_);
lean_dec(v_declName_1562_);
v___y_1577_ = v_a_1564_;
v___y_1578_ = v_a_1565_;
v___y_1579_ = v_a_1566_;
v___y_1580_ = v_a_1567_;
goto v___jp_1576_;
}
v___jp_1576_:
{
uint8_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = 0;
v___x_1582_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1571_, v___f_1575_, v___x_1581_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1582_;
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v___x_1571_);
lean_dec(v_declName_1562_);
v_a_1591_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1572_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1572_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_declName_1562_);
v_a_1599_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1569_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1569_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___boxed(lean_object* v_declName_1607_, lean_object* v_attrKind_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
uint8_t v_attrKind_boxed_1614_; lean_object* v_res_1615_; 
v_attrKind_boxed_1614_ = lean_unbox(v_attrKind_1608_);
v_res_1615_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_1607_, v_attrKind_boxed_1614_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
return v_res_1615_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(lean_object* v_xs_1616_, lean_object* v_ys_1617_, lean_object* v_hsz_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1616_, v_ys_1617_, v_x_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___boxed(lean_object* v_xs_1622_, lean_object* v_ys_1623_, lean_object* v_hsz_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(v_xs_1622_, v_ys_1623_, v_hsz_1624_, v_x_1625_, v_x_1626_);
lean_dec_ref(v_ys_1623_);
lean_dec_ref(v_xs_1622_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(lean_object* v_as_1629_, size_t v_i_1630_, size_t v_stop_1631_, lean_object* v_b_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1629_, v_i_1630_, v_stop_1631_, v_b_1632_, v___y_1633_, v___y_1635_, v___y_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___boxed(lean_object* v_as_1639_, lean_object* v_i_1640_, lean_object* v_stop_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
size_t v_i_boxed_1648_; size_t v_stop_boxed_1649_; lean_object* v_res_1650_; 
v_i_boxed_1648_ = lean_unbox_usize(v_i_1640_);
lean_dec(v_i_1640_);
v_stop_boxed_1649_ = lean_unbox_usize(v_stop_1641_);
lean_dec(v_stop_1641_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(v_as_1639_, v_i_boxed_1648_, v_stop_boxed_1649_, v_b_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v_as_1639_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(lean_object* v___x_1651_, lean_object* v_as_x27_1652_, lean_object* v_b_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
if (lean_obj_tag(v_as_x27_1652_) == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_b_1653_);
return v___x_1659_;
}
else
{
lean_object* v_head_1660_; lean_object* v_tail_1661_; lean_object* v___y_1663_; uint8_t v___y_1664_; lean_object* v_a_1668_; lean_object* v_declName_1671_; lean_object* v_arity_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_head_1660_ = lean_ctor_get(v_as_x27_1652_, 0);
v_tail_1661_ = lean_ctor_get(v_as_x27_1652_, 1);
v_declName_1671_ = lean_ctor_get(v_head_1660_, 0);
v_arity_1672_ = lean_ctor_get(v_head_1660_, 1);
v___x_1673_ = lean_array_get_size(v___x_1651_);
v___x_1674_ = lean_nat_dec_le(v_arity_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
v_as_x27_1652_ = v_tail_1661_;
goto _start;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_nat_sub(v___x_1673_, v_arity_1672_);
v___x_1677_ = l_Array_extract___redArg(v___x_1651_, v___x_1676_, v___x_1673_);
lean_inc(v_declName_1671_);
v___x_1678_ = l_Lean_Meta_mkAppM(v_declName_1671_, v___x_1677_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_n(v_a_1679_, 2);
lean_dec_ref_known(v___x_1678_, 1);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
v___x_1680_ = lean_infer_type(v_a_1679_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_a_1679_);
lean_ctor_set(v___x_1682_, 1, v_a_1681_);
v___x_1683_ = lean_array_push(v_b_1653_, v___x_1682_);
v_as_x27_1652_ = v_tail_1661_;
v_b_1653_ = v___x_1683_;
goto _start;
}
else
{
lean_object* v_a_1685_; 
lean_dec(v_a_1679_);
v_a_1685_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1680_, 1);
v_a_1668_ = v_a_1685_;
goto v___jp_1667_;
}
}
else
{
lean_object* v_a_1686_; 
v_a_1686_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1678_, 1);
v_a_1668_ = v_a_1686_;
goto v___jp_1667_;
}
}
v___jp_1662_:
{
if (v___y_1664_ == 0)
{
lean_dec_ref(v___y_1663_);
v_as_x27_1652_ = v_tail_1661_;
goto _start;
}
else
{
lean_object* v___x_1666_; 
lean_dec_ref(v_b_1653_);
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___y_1663_);
return v___x_1666_;
}
}
v___jp_1667_:
{
uint8_t v___x_1669_; 
v___x_1669_ = l_Lean_Exception_isInterrupt(v_a_1668_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; 
lean_inc_ref(v_a_1668_);
v___x_1670_ = l_Lean_Exception_isRuntime(v_a_1668_);
v___y_1663_ = v_a_1668_;
v___y_1664_ = v___x_1670_;
goto v___jp_1662_;
}
else
{
v___y_1663_ = v_a_1668_;
v___y_1664_ = v___x_1669_;
goto v___jp_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg___boxed(lean_object* v___x_1687_, lean_object* v_as_x27_1688_, lean_object* v_b_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1687_, v_as_x27_1688_, v_b_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v_as_x27_1688_);
lean_dec_ref(v___x_1687_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object* v_e_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Expr_getAppFn(v_e_1698_);
if (lean_obj_tag(v___x_1704_) == 4)
{
lean_object* v_declName_1705_; lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1725_; 
v_declName_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_declName_1705_);
lean_dec_ref_known(v___x_1704_, 2);
v___x_1706_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1702_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1725_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1725_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1707_, v_declName_1705_);
lean_dec(v_declName_1705_);
lean_dec(v_a_1707_);
if (lean_obj_tag(v___x_1711_) == 1)
{
lean_object* v_val_1712_; lean_object* v_dummy_1713_; lean_object* v_nargs_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_del_object(v___x_1709_);
v_val_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_val_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v_dummy_1713_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1714_ = l_Lean_Expr_getAppNumArgs(v_e_1698_);
lean_inc(v_nargs_1714_);
v___x_1715_ = lean_mk_array(v_nargs_1714_, v_dummy_1713_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_sub(v_nargs_1714_, v___x_1716_);
lean_dec(v_nargs_1714_);
v___x_1718_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1698_, v___x_1715_, v___x_1717_);
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1720_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1718_, v_val_1712_, v___x_1719_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_val_1712_);
lean_dec_ref(v___x_1718_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
lean_dec(v___x_1711_);
lean_dec_ref(v_e_1698_);
v___x_1721_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1721_);
v___x_1723_ = v___x_1709_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___x_1704_);
lean_dec_ref(v_e_1698_);
v___x_1726_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___boxed(lean_object* v_e_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(lean_object* v___x_1735_, lean_object* v_as_1736_, lean_object* v_as_x27_1737_, lean_object* v_b_1738_, lean_object* v_a_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1735_, v_as_x27_1737_, v_b_1738_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___boxed(lean_object* v___x_1746_, lean_object* v_as_1747_, lean_object* v_as_x27_1748_, lean_object* v_b_1749_, lean_object* v_a_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(v___x_1746_, v_as_1747_, v_as_x27_1748_, v_b_1749_, v_a_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v_as_x27_1748_);
lean_dec(v_as_1747_);
lean_dec_ref(v___x_1746_);
return v_res_1756_;
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
