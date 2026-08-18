// Lean compiler output
// Module: Lean.Meta.Sym.SymM
// Imports: public import Lean.Meta.Sym.AlphaShareCommon public import Lean.Meta.CongrTheorems public import Lean.Meta.Transform import Lean.Meta.WHNF import Lean.Meta.AppBuilder
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 1, 190, 45, 30, 82, 81, 176)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "check invariants"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 148, 146, 121, 82, 137, 202, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(81, 198, 26, 180, 162, 99, 75, 86)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_sym_debug;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "issues"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 90, 109, 68, 195, 255, 174, 185)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(215, 84, 158, 71, 120, 158, 242, 63)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "SymM"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 120, 93, 45, 98, 183, 49, 234)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 107, 0, 166, 43, 148, 190, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(250, 253, 133, 58, 166, 2, 152, 17)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 230, 149, 24, 177, 0, 168, 74)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(247, 70, 210, 197, 64, 19, 25, 35)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 119, 254, 183, 253, 57, 73, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 29, 178, 129, 13, 184, 131, 91)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(138, 150, 153, 124, 1, 171, 141, 81)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(46, 97, 109, 246, 28, 99, 14, 68)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(231, 39, 117, 214, 12, 215, 126, 174)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 149, 253, 44, 239, 131, 52, 47)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_SymExtensionStateSpec = (const lean_object*)&l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtensionState;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "failed to register `Sym` extension, extensions can only be registered during initialization"};
static const lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
static const lean_array_object l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducibleStep___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__2;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isProj___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_foldProjs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_foldProjs___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Ordering"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 86, 2, 28, 163, 164, 77)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.Sym.SymM"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.SymM.run"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Sym.shareCommonWithoutChecks"};
static const lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "internal error, expression has loose bound variables at `shareCommon`"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_reportIssue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "issue"};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_reportIssue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 190, 118, 187, 186, 110, 108, 236)}};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_reportIssue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_reportIssue___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Sym.reportIssueIfVerbose"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "reportIssueIfVerbose"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 254, 137, 8, 139, 198, 210, 169)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 43, 55, 72, 125, 82, 73, 158)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 165, 116, 130, 189, 215, 142, 41)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "doElemReportIssue!__"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 149, 154, 203, 214, 83, 169, 43)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reportIssue!"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21____ = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Sym.reportDbgIssue"};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1;
static const lean_string_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reportDbgIssue"};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 254, 137, 8, 139, 198, 210, 169)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 136, 27, 81, 109, 98, 120, 61)}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 182, 25, 82, 56, 230, 186, 254)}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "doElemReportDbgIssue!__"};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 81, 179, 30, 51, 192, 195, 77)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reportDbgIssue!"};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21____ = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__4;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__5;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__11;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__12_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__13_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__14_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__21;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymM___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "<SymM default value>"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
return v_res_60_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2410647589u);
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_119_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_120_ = l_Lean_Name_str___override(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_123_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_124_ = l_Lean_Name_str___override(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_127_ = l_Lean_Name_num___override(v___x_126_, v___x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_130_ = 0;
v___x_131_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_132_ = l_Lean_registerTraceClass(v___x_129_, v___x_130_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
return v_res_134_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState(void){
_start:
{
lean_object* v___x_138_; lean_object* v_snd_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Sym_SymExtensionStateSpec));
v_snd_139_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_snd_139_);
return v_snd_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1));
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed(lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object* v_00_u03c3_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1));
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_box(0));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_));
v___x_161_ = lean_st_mk_ref(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object* v_ext_165_){
_start:
{
lean_inc_ref(v_ext_165_);
return v_ext_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object* v_ext_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(v_ext_166_);
lean_dec_ref(v_ext_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object* v_00_u03c3_168_, lean_object* v_ext_169_){
_start:
{
lean_inc_ref(v_ext_169_);
return v_ext_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object* v_00_u03c3_170_, lean_object* v_ext_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(v_00_u03c3_170_, v_ext_171_);
lean_dec_ref(v_ext_171_);
return v_res_172_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0));
v___x_175_ = lean_mk_io_user_error(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object* v_mkInitial_176_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_initializing();
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref(v_mkInitial_176_);
v___x_179_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_181_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_182_ = lean_st_ref_get(v___x_181_);
v___x_183_ = lean_st_ref_take(v___x_181_);
v___x_184_ = lean_array_get_size(v___x_182_);
lean_dec(v___x_182_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_mkInitial_176_);
lean_inc_ref(v___x_185_);
v___x_186_ = lean_array_push(v___x_183_, v___x_185_);
v___x_187_ = lean_st_ref_put(v___x_181_, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_185_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_192_, lean_object* v_mkInitial_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_196_, lean_object* v_mkInitial_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_196_, v_mkInitial_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_200_, size_t v_i_201_, lean_object* v_bs_202_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_201_, v_sz_200_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v_bs_202_);
return v___x_205_;
}
else
{
lean_object* v_v_206_; lean_object* v_mkInitial_207_; lean_object* v___x_208_; 
v_v_206_ = lean_array_uget_borrowed(v_bs_202_, v_i_201_);
v_mkInitial_207_ = lean_ctor_get(v_v_206_, 1);
lean_inc_ref(v_mkInitial_207_);
v___x_208_ = lean_apply_1(v_mkInitial_207_, lean_box(0));
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v_bs_x27_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = lean_unsigned_to_nat(0u);
v_bs_x27_211_ = lean_array_uset(v_bs_202_, v_i_201_, v___x_210_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_201_, v___x_212_);
v___x_214_ = lean_array_uset(v_bs_x27_211_, v_i_201_, v_a_209_);
v_i_201_ = v___x_213_;
v_bs_202_ = v___x_214_;
goto _start;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_bs_202_);
v_a_216_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_208_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_208_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object* v_sz_224_, lean_object* v_i_225_, lean_object* v_bs_226_, lean_object* v___y_227_){
_start:
{
size_t v_sz_boxed_228_; size_t v_i_boxed_229_; lean_object* v_res_230_; 
v_sz_boxed_228_ = lean_unbox_usize(v_sz_224_);
lean_dec(v_sz_224_);
v_i_boxed_229_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_228_, v_i_boxed_229_, v_bs_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; size_t v_sz_234_; size_t v___x_235_; lean_object* v___x_236_; 
v___x_232_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_233_ = lean_st_ref_get(v___x_232_);
v_sz_234_ = lean_array_size(v___x_233_);
v___x_235_ = ((size_t)0ULL);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_234_, v___x_235_, v___x_233_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object* v_x_247_){
_start:
{
switch(lean_obj_tag(v_x_247_))
{
case 0:
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(0u);
return v___x_248_;
}
case 1:
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(1u);
return v___x_249_;
}
case 2:
{
lean_object* v___x_250_; 
v___x_250_ = lean_unsigned_to_nat(2u);
return v___x_250_;
}
default: 
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(3u);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_252_);
lean_dec(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
switch(lean_obj_tag(v_t_254_))
{
case 0:
{
return v_k_255_;
}
case 1:
{
lean_object* v_prefixSize_256_; lean_object* v_suffixSize_257_; lean_object* v___x_258_; 
v_prefixSize_256_ = lean_ctor_get(v_t_254_, 0);
lean_inc(v_prefixSize_256_);
v_suffixSize_257_ = lean_ctor_get(v_t_254_, 1);
lean_inc(v_suffixSize_257_);
lean_dec_ref_known(v_t_254_, 2);
v___x_258_ = lean_apply_2(v_k_255_, v_prefixSize_256_, v_suffixSize_257_);
return v___x_258_;
}
default: 
{
lean_object* v_rewritable_259_; lean_object* v___x_260_; 
v_rewritable_259_ = lean_ctor_get(v_t_254_, 0);
lean_inc_ref(v_rewritable_259_);
lean_dec(v_t_254_);
v___x_260_ = lean_apply_1(v_k_255_, v_rewritable_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_261_, lean_object* v_ctorIdx_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_k_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_263_, v_k_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_267_, lean_object* v_ctorIdx_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_k_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_267_, v_ctorIdx_268_, v_t_269_, v_h_270_, v_k_271_);
lean_dec(v_ctorIdx_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_273_, lean_object* v_none_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_273_, v_none_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_none_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_277_, v_none_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_281_, lean_object* v_fixedPrefix_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_281_, v_fixedPrefix_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_fixedPrefix_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_285_, v_fixedPrefix_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_289_, lean_object* v_interlaced_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_289_, v_interlaced_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_interlaced_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_293_, v_interlaced_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_297_, lean_object* v_congrTheorem_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_297_, v_congrTheorem_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_congrTheorem_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_301_, v_congrTheorem_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Expr_getAppFn(v_e_311_);
if (lean_obj_tag(v___x_317_) == 4)
{
lean_object* v_declName_318_; lean_object* v___x_319_; lean_object* v_env_320_; uint8_t v___x_321_; 
v_declName_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_declName_318_);
lean_dec_ref_known(v___x_317_, 2);
v___x_319_ = lean_st_ref_get(v_a_315_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_320_, v_declName_318_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_e_311_);
v___x_322_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
else
{
uint8_t v___x_324_; lean_object* v___x_325_; 
v___x_324_ = 0;
v___x_325_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_311_, v___x_324_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_345_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_345_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_345_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_345_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
if (lean_obj_tag(v_a_326_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_340_; 
v_val_330_ = lean_ctor_get(v_a_326_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_a_326_);
if (v_isSharedCheck_340_ == 0)
{
v___x_332_ = v_a_326_;
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_dec(v_a_326_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_val_330_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_335_);
v___x_337_ = v___x_328_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_a_326_);
v___x_341_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_341_);
v___x_343_ = v___x_328_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_325_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_325_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v___x_317_);
lean_dec_ref(v_e_311_);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_362_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_363_, lean_object* v_e_364_){
_start:
{
if (lean_obj_tag(v_e_364_) == 4)
{
lean_object* v_declName_365_; uint8_t v___x_366_; 
v_declName_365_ = lean_ctor_get(v_e_364_, 0);
lean_inc(v_declName_365_);
lean_dec_ref_known(v_e_364_, 2);
v___x_366_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_363_, v_declName_365_);
return v___x_366_;
}
else
{
uint8_t v___x_367_; 
lean_dec_ref(v_e_364_);
lean_dec_ref(v_env_363_);
v___x_367_ = 0;
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_368_, lean_object* v_e_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_368_, v_e_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_env_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v___x_375_ = lean_st_ref_get(v_a_373_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_377_, 0, v_env_376_);
v___x_378_ = lean_find_expr(v___f_377_, v_e_372_);
lean_dec_ref(v___f_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = 0;
v___x_380_ = lean_box(v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_378_, 0);
lean_dec(v_unused_391_);
v___x_383_ = v___x_378_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_dec(v___x_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = 1;
v___x_386_ = lean_box(v___x_385_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 0);
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_e_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_396_, v_a_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec_ref(v_e_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_e_406_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_421_, lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_apply_1(v_x_422_, lean_box(0));
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_430_, v_x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_m_438_, lean_object* v_query_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v_zero_443_; uint8_t v_isZero_444_; 
v_zero_443_ = lean_unsigned_to_nat(0u);
v_isZero_444_ = lean_nat_dec_eq(v_x_441_, v_zero_443_);
if (v_isZero_444_ == 1)
{
lean_dec(v_x_442_);
lean_dec(v_x_441_);
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(2);
return v___x_445_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_val_446_ = lean_ctor_get(v_x_440_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v_x_440_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_x_440_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_val_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_keyArray_454_; lean_object* v_valueArray_455_; lean_object* v___x_456_; uint8_t v_isSome_457_; 
v_keyArray_454_ = lean_ctor_get(v_m_438_, 1);
v_valueArray_455_ = lean_ctor_get(v_m_438_, 2);
v___x_456_ = lean_array_fget_borrowed(v_keyArray_454_, v_x_442_);
v_isSome_457_ = lean_noption_is_some(v___x_456_);
if (v_isSome_457_ == 0)
{
lean_dec(v_x_441_);
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_x_442_);
return v___x_458_;
}
else
{
lean_object* v_val_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_x_442_);
v_val_459_ = lean_ctor_get(v_x_440_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v_x_440_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_val_459_);
lean_dec(v_x_440_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_val_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_one_467_; lean_object* v_n_468_; lean_object* v___y_470_; 
v_one_467_ = lean_unsigned_to_nat(1u);
v_n_468_ = lean_nat_sub(v_x_441_, v_one_467_);
lean_dec(v_x_441_);
if (v_isSome_457_ == 0)
{
goto v___jp_476_;
}
else
{
lean_object* v___x_478_; uint8_t v_isSome_479_; 
v___x_478_ = lean_array_fget_borrowed(v_valueArray_455_, v_x_442_);
v_isSome_479_ = lean_noption_is_some(v___x_478_);
if (v_isSome_479_ == 0)
{
goto v___jp_476_;
}
else
{
lean_object* v_val_480_; uint8_t v___x_481_; 
lean_inc(v___x_456_);
v_val_480_ = lean_noption_get(v___x_456_);
v___x_481_ = l_Lean_ExprStructEq_beq(v_val_480_, v_query_439_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
lean_dec(v_val_480_);
v___x_482_ = lean_array_get_size(v_keyArray_454_);
v___x_483_ = lean_nat_add(v_x_442_, v_one_467_);
lean_dec(v_x_442_);
v___x_484_ = lean_nat_dec_lt(v___x_483_, v___x_482_);
if (v___x_484_ == 0)
{
lean_dec(v___x_483_);
v_x_441_ = v_n_468_;
v_x_442_ = v_zero_443_;
goto _start;
}
else
{
v_x_441_ = v_n_468_;
v_x_442_ = v___x_483_;
goto _start;
}
}
else
{
lean_object* v_val_487_; lean_object* v___x_488_; 
lean_dec(v_n_468_);
lean_dec(v_x_440_);
lean_inc(v___x_478_);
v_val_487_ = lean_noption_get(v___x_478_);
v___x_488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_488_, 0, v_x_442_);
lean_ctor_set(v___x_488_, 1, v_val_480_);
lean_ctor_set(v___x_488_, 2, v_val_487_);
return v___x_488_;
}
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_array_get_size(v_keyArray_454_);
v___x_472_ = lean_nat_add(v_x_442_, v_one_467_);
lean_dec(v_x_442_);
v___x_473_ = lean_nat_dec_lt(v___x_472_, v___x_471_);
if (v___x_473_ == 0)
{
lean_dec(v___x_472_);
v_x_440_ = v___y_470_;
v_x_441_ = v_n_468_;
v_x_442_ = v_zero_443_;
goto _start;
}
else
{
v_x_440_ = v___y_470_;
v_x_441_ = v_n_468_;
v_x_442_ = v___x_472_;
goto _start;
}
}
v___jp_476_:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v___x_477_; 
lean_inc(v_x_442_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_x_442_);
v___y_470_ = v___x_477_;
goto v___jp_469_;
}
else
{
v___y_470_ = v_x_440_;
goto v___jp_469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_m_489_, lean_object* v_query_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_m_489_, v_query_490_, v_x_491_, v_x_492_, v_x_493_);
lean_dec_ref(v_query_490_);
lean_dec_ref(v_m_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_495_, lean_object* v_query_496_){
_start:
{
lean_object* v_keyArray_497_; lean_object* v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v_fold_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_keyArray_497_ = lean_ctor_get(v_m_495_, 1);
v___x_498_ = lean_array_get_size(v_keyArray_497_);
v___x_499_ = l_Lean_ExprStructEq_hash(v_query_496_);
v___x_500_ = 32ULL;
v___x_501_ = lean_uint64_shift_right(v___x_499_, v___x_500_);
v_fold_502_ = lean_uint64_xor(v___x_499_, v___x_501_);
v___x_503_ = 16ULL;
v___x_504_ = lean_uint64_shift_right(v_fold_502_, v___x_503_);
v___x_505_ = lean_uint64_xor(v_fold_502_, v___x_504_);
v___x_506_ = lean_uint64_to_usize(v___x_505_);
v___x_507_ = lean_usize_of_nat(v___x_498_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_sub(v___x_507_, v___x_508_);
v___x_510_ = lean_usize_land(v___x_506_, v___x_509_);
v___x_511_ = lean_usize_to_nat(v___x_510_);
v___x_512_ = lean_box(0);
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_m_495_, v_query_496_, v___x_512_, v___x_498_, v___x_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg___boxed(lean_object* v_m_514_, lean_object* v_query_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_514_, v_query_515_);
lean_dec_ref(v_query_515_);
lean_dec_ref(v_m_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(lean_object* v_b_517_, lean_object* v_acc_518_, lean_object* v_i_519_){
_start:
{
lean_object* v___y_521_; lean_object* v_keyArray_529_; lean_object* v_valueArray_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_keyArray_529_ = lean_ctor_get(v_b_517_, 1);
v_valueArray_530_ = lean_ctor_get(v_b_517_, 2);
v___x_531_ = lean_array_get_size(v_keyArray_529_);
v___x_532_ = lean_nat_dec_lt(v_i_519_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec(v_i_519_);
return v_acc_518_;
}
else
{
lean_object* v___x_533_; uint8_t v_isSome_534_; 
v___x_533_ = lean_array_fget_borrowed(v_keyArray_529_, v_i_519_);
v_isSome_534_ = lean_noption_is_some(v___x_533_);
if (v_isSome_534_ == 0)
{
goto v___jp_525_;
}
else
{
lean_object* v___x_535_; uint8_t v_isSome_536_; 
v___x_535_ = lean_array_fget_borrowed(v_valueArray_530_, v_i_519_);
v_isSome_536_ = lean_noption_is_some(v___x_535_);
if (v_isSome_536_ == 0)
{
goto v___jp_525_;
}
else
{
lean_object* v_val_537_; lean_object* v_val_538_; lean_object* v_i_540_; lean_object* v___x_545_; 
lean_inc(v___x_533_);
v_val_537_ = lean_noption_get(v___x_533_);
lean_inc(v___x_535_);
v_val_538_ = lean_noption_get(v___x_535_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_acc_518_, v_val_537_);
switch(lean_obj_tag(v___x_545_))
{
case 0:
{
lean_object* v_index_546_; lean_object* v_size_547_; lean_object* v___x_548_; 
v_index_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_545_, 3);
v_size_547_ = lean_ctor_get(v_acc_518_, 0);
lean_inc(v_size_547_);
v___x_548_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_518_, v_size_547_, v_index_546_, v_val_537_, v_val_538_);
lean_dec(v_index_546_);
v___y_521_ = v___x_548_;
goto v___jp_520_;
}
case 1:
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_545_, 1);
v_i_540_ = v_index_549_;
goto v___jp_539_;
}
default: 
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_518_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_index_552_; 
v_index_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_index_552_);
lean_dec_ref_known(v___x_551_, 1);
v_i_540_ = v_index_552_;
goto v___jp_539_;
}
else
{
lean_dec(v_val_538_);
lean_dec(v_val_537_);
v___y_521_ = v_acc_518_;
goto v___jp_520_;
}
}
}
v___jp_539_:
{
lean_object* v_size_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_size_541_ = lean_ctor_get(v_acc_518_, 0);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_size_541_, v___x_542_);
v___x_544_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_518_, v___x_543_, v_i_540_, v_val_537_, v_val_538_);
lean_dec(v_i_540_);
v___y_521_ = v___x_544_;
goto v___jp_520_;
}
}
}
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_519_, v___x_522_);
lean_dec(v_i_519_);
v_acc_518_ = v___y_521_;
v_i_519_ = v___x_523_;
goto _start;
}
v___jp_525_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_i_519_, v___x_526_);
lean_dec(v_i_519_);
v_i_519_ = v___x_527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg___boxed(lean_object* v_b_553_, lean_object* v_acc_554_, lean_object* v_i_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(v_b_553_, v_acc_554_, v_i_555_);
lean_dec_ref(v_b_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg(lean_object* v_init_557_, lean_object* v_b_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(v_b_558_, v_init_557_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg___boxed(lean_object* v_init_561_, lean_object* v_b_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg(v_init_561_, v_b_562_);
lean_dec_ref(v_b_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(lean_object* v_m_564_){
_start:
{
lean_object* v_keyArray_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_cellCount_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_target_572_; lean_object* v___x_573_; 
v_keyArray_565_ = lean_ctor_get(v_m_564_, 1);
v___x_566_ = lean_array_get_size(v_keyArray_565_);
v___x_567_ = lean_unsigned_to_nat(2u);
v_cellCount_568_ = lean_nat_mul(v___x_566_, v___x_567_);
v___x_569_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_568_);
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_568_);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_568_);
v_target_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_572_, 0, v___x_569_);
lean_ctor_set(v_target_572_, 1, v___x_570_);
lean_ctor_set(v_target_572_, 2, v___x_571_);
v___x_573_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg(v_target_572_, v_m_564_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg___boxed(lean_object* v_m_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(v_m_574_);
lean_dec_ref(v_m_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_576_, lean_object* v_e_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___y_583_; lean_object* v___y_586_; lean_object* v_i_587_; lean_object* v___y_603_; lean_object* v_i_604_; lean_object* v___y_610_; lean_object* v___x_619_; 
v___x_580_ = lean_st_ref_take(v_a_576_);
v___x_581_ = lean_box(0);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_580_, v_e_577_);
switch(lean_obj_tag(v___x_619_))
{
case 0:
{
lean_object* v_index_620_; lean_object* v_size_621_; lean_object* v___x_622_; 
v_index_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_index_620_);
lean_dec_ref_known(v___x_619_, 3);
v_size_621_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_size_621_);
v___x_622_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_580_, v_size_621_, v_index_620_, v_e_577_, v_a_578_);
lean_dec(v_index_620_);
v___y_583_ = v___x_622_;
goto v___jp_582_;
}
case 1:
{
lean_object* v_index_623_; lean_object* v_size_624_; lean_object* v_keyArray_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_index_623_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_index_623_);
lean_dec_ref_known(v___x_619_, 1);
v_size_624_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_size_624_);
v_keyArray_625_ = lean_ctor_get(v___x_580_, 1);
lean_inc_ref(v_keyArray_625_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_size_624_, v___x_626_);
lean_dec(v_size_624_);
v___x_628_ = lean_array_get_size(v_keyArray_625_);
lean_dec_ref(v_keyArray_625_);
v___x_629_ = lean_nat_dec_lt(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v___x_627_);
lean_dec(v_index_623_);
goto v___jp_592_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_630_ = lean_unsigned_to_nat(4u);
v___x_631_ = lean_nat_mul(v___x_627_, v___x_630_);
v___x_632_ = lean_unsigned_to_nat(3u);
v___x_633_ = lean_nat_mul(v___x_628_, v___x_632_);
v___x_634_ = lean_nat_dec_le(v___x_631_, v___x_633_);
lean_dec(v___x_633_);
lean_dec(v___x_631_);
if (v___x_634_ == 0)
{
lean_dec(v___x_627_);
lean_dec(v_index_623_);
goto v___jp_592_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_580_, v___x_627_, v_index_623_, v_e_577_, v_a_578_);
lean_dec(v_index_623_);
v___y_583_ = v___x_635_;
goto v___jp_582_;
}
}
}
default: 
{
lean_object* v_size_636_; lean_object* v_keyArray_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_size_636_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_size_636_);
v_keyArray_637_ = lean_ctor_get(v___x_580_, 1);
lean_inc_ref(v_keyArray_637_);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_size_636_, v___x_638_);
lean_dec(v_size_636_);
v___x_640_ = lean_array_get_size(v_keyArray_637_);
lean_dec_ref(v_keyArray_637_);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec(v___x_639_);
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(v___x_580_);
lean_dec(v___x_580_);
v___y_610_ = v___x_642_;
goto v___jp_609_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = lean_nat_mul(v___x_639_, v___x_643_);
lean_dec(v___x_639_);
v___x_645_ = lean_unsigned_to_nat(3u);
v___x_646_ = lean_nat_mul(v___x_640_, v___x_645_);
v___x_647_ = lean_nat_dec_le(v___x_644_, v___x_646_);
lean_dec(v___x_646_);
lean_dec(v___x_644_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(v___x_580_);
lean_dec(v___x_580_);
v___y_610_ = v___x_648_;
goto v___jp_609_;
}
else
{
v___y_610_ = v___x_580_;
goto v___jp_609_;
}
}
}
}
v___jp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_st_ref_put(v_a_576_, v___y_583_);
return v___x_581_;
}
v___jp_585_:
{
lean_object* v_size_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_size_588_ = lean_ctor_get(v___y_586_, 0);
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_size_588_, v___x_589_);
v___x_591_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_586_, v___x_590_, v_i_587_, v_e_577_, v_a_578_);
lean_dec(v_i_587_);
v___y_583_ = v___x_591_;
goto v___jp_582_;
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(v___x_580_);
lean_dec(v___x_580_);
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_593_, v_e_577_);
switch(lean_obj_tag(v___x_594_))
{
case 0:
{
lean_object* v_index_595_; lean_object* v_size_596_; lean_object* v___x_597_; 
v_index_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_index_595_);
lean_dec_ref_known(v___x_594_, 3);
v_size_596_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_size_596_);
v___x_597_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_593_, v_size_596_, v_index_595_, v_e_577_, v_a_578_);
lean_dec(v_index_595_);
v___y_583_ = v___x_597_;
goto v___jp_582_;
}
case 1:
{
lean_object* v_index_598_; 
v_index_598_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_index_598_);
lean_dec_ref_known(v___x_594_, 1);
v___y_586_ = v___x_593_;
v_i_587_ = v_index_598_;
goto v___jp_585_;
}
default: 
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_593_, v___x_599_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_index_601_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 1);
v___y_586_ = v___x_593_;
v_i_587_ = v_index_601_;
goto v___jp_585_;
}
else
{
lean_dec_ref(v_a_578_);
lean_dec_ref(v_e_577_);
v___y_583_ = v___x_593_;
goto v___jp_582_;
}
}
}
}
v___jp_602_:
{
lean_object* v_size_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_size_605_ = lean_ctor_get(v___y_603_, 0);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_size_605_, v___x_606_);
v___x_608_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_603_, v___x_607_, v_i_604_, v_e_577_, v_a_578_);
lean_dec(v_i_604_);
v___y_583_ = v___x_608_;
goto v___jp_582_;
}
v___jp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___y_610_, v_e_577_);
switch(lean_obj_tag(v___x_611_))
{
case 0:
{
lean_object* v_index_612_; lean_object* v_size_613_; lean_object* v___x_614_; 
v_index_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_index_612_);
lean_dec_ref_known(v___x_611_, 3);
v_size_613_ = lean_ctor_get(v___y_610_, 0);
lean_inc(v_size_613_);
v___x_614_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_610_, v_size_613_, v_index_612_, v_e_577_, v_a_578_);
lean_dec(v_index_612_);
v___y_583_ = v___x_614_;
goto v___jp_582_;
}
case 1:
{
lean_object* v_index_615_; 
v_index_615_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_index_615_);
lean_dec_ref_known(v___x_611_, 1);
v___y_603_ = v___y_610_;
v_i_604_ = v_index_615_;
goto v___jp_602_;
}
default: 
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_610_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_index_618_; 
v_index_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_618_);
lean_dec_ref_known(v___x_617_, 1);
v___y_603_ = v___y_610_;
v_i_604_ = v_index_618_;
goto v___jp_602_;
}
else
{
lean_dec_ref(v_a_578_);
lean_dec_ref(v_e_577_);
v___y_583_ = v___y_610_;
goto v___jp_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_649_, lean_object* v_e_650_, lean_object* v_a_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_649_, v_e_650_, v_a_651_);
lean_dec(v_a_649_);
return v_res_653_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Lean_maxRecDepthErrorMessage;
v___x_660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_662_ = l_Lean_MessageData_ofFormat(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_664_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_665_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_ref_666_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___y_682_; lean_object* v_fileName_691_; lean_object* v_fileMap_692_; lean_object* v_options_693_; lean_object* v_currRecDepth_694_; lean_object* v_maxRecDepth_695_; lean_object* v_ref_696_; lean_object* v_currNamespace_697_; lean_object* v_openDecls_698_; lean_object* v_initHeartbeats_699_; lean_object* v_maxHeartbeats_700_; lean_object* v_quotContext_701_; lean_object* v_currMacroScope_702_; uint8_t v_diag_703_; lean_object* v_cancelTk_x3f_704_; uint8_t v_suppressElabErrors_705_; lean_object* v_inheritedTraceOptions_706_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_fileName_691_ = lean_ctor_get(v___y_678_, 0);
v_fileMap_692_ = lean_ctor_get(v___y_678_, 1);
v_options_693_ = lean_ctor_get(v___y_678_, 2);
v_currRecDepth_694_ = lean_ctor_get(v___y_678_, 3);
v_maxRecDepth_695_ = lean_ctor_get(v___y_678_, 4);
v_ref_696_ = lean_ctor_get(v___y_678_, 5);
v_currNamespace_697_ = lean_ctor_get(v___y_678_, 6);
v_openDecls_698_ = lean_ctor_get(v___y_678_, 7);
v_initHeartbeats_699_ = lean_ctor_get(v___y_678_, 8);
v_maxHeartbeats_700_ = lean_ctor_get(v___y_678_, 9);
v_quotContext_701_ = lean_ctor_get(v___y_678_, 10);
v_currMacroScope_702_ = lean_ctor_get(v___y_678_, 11);
v_diag_703_ = lean_ctor_get_uint8(v___y_678_, sizeof(void*)*14);
v_cancelTk_x3f_704_ = lean_ctor_get(v___y_678_, 12);
v_suppressElabErrors_705_ = lean_ctor_get_uint8(v___y_678_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_706_ = lean_ctor_get(v___y_678_, 13);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_nat_dec_eq(v_maxRecDepth_695_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; 
v___x_714_ = lean_nat_dec_eq(v_currRecDepth_694_, v_maxRecDepth_695_);
if (v___x_714_ == 0)
{
goto v___jp_707_;
}
else
{
lean_object* v___x_715_; 
lean_dec_ref(v_x_674_);
lean_inc(v_ref_696_);
v___x_715_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_696_);
v___y_682_ = v___x_715_;
goto v___jp_681_;
}
}
else
{
goto v___jp_707_;
}
v___jp_681_:
{
if (lean_obj_tag(v___y_682_) == 0)
{
return v___y_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___y_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___y_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___y_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___y_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_currRecDepth_694_, v___x_708_);
lean_inc_ref(v_inheritedTraceOptions_706_);
lean_inc(v_cancelTk_x3f_704_);
lean_inc(v_currMacroScope_702_);
lean_inc(v_quotContext_701_);
lean_inc(v_maxHeartbeats_700_);
lean_inc(v_initHeartbeats_699_);
lean_inc(v_openDecls_698_);
lean_inc(v_currNamespace_697_);
lean_inc(v_ref_696_);
lean_inc(v_maxRecDepth_695_);
lean_inc_ref(v_options_693_);
lean_inc_ref(v_fileMap_692_);
lean_inc_ref(v_fileName_691_);
v___x_710_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_710_, 0, v_fileName_691_);
lean_ctor_set(v___x_710_, 1, v_fileMap_692_);
lean_ctor_set(v___x_710_, 2, v_options_693_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
lean_ctor_set(v___x_710_, 4, v_maxRecDepth_695_);
lean_ctor_set(v___x_710_, 5, v_ref_696_);
lean_ctor_set(v___x_710_, 6, v_currNamespace_697_);
lean_ctor_set(v___x_710_, 7, v_openDecls_698_);
lean_ctor_set(v___x_710_, 8, v_initHeartbeats_699_);
lean_ctor_set(v___x_710_, 9, v_maxHeartbeats_700_);
lean_ctor_set(v___x_710_, 10, v_quotContext_701_);
lean_ctor_set(v___x_710_, 11, v_currMacroScope_702_);
lean_ctor_set(v___x_710_, 12, v_cancelTk_x3f_704_);
lean_ctor_set(v___x_710_, 13, v_inheritedTraceOptions_706_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*14, v_diag_703_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*14 + 1, v_suppressElabErrors_705_);
lean_inc(v___y_679_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
v___x_711_ = lean_apply_6(v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___x_710_, v___y_679_, lean_box(0));
v___y_682_ = v___x_711_;
goto v___jp_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_724_, lean_object* v_x_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_apply_1(v_x_725_, lean_box(0));
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_733_, lean_object* v_x_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_733_, v_x_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_m_741_, lean_object* v_query_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_741_, v_query_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_index_744_; lean_object* v_key_745_; lean_object* v_value_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_index_744_ = lean_ctor_get(v___x_743_, 0);
v_key_745_ = lean_ctor_get(v___x_743_, 1);
v_value_746_ = lean_ctor_get(v___x_743_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_743_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_value_746_);
lean_inc(v_key_745_);
lean_inc(v_index_744_);
lean_dec(v___x_743_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_index_744_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_key_745_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_value_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v___x_754_; 
lean_dec(v___x_743_);
v___x_754_ = lean_box(1);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_m_755_, lean_object* v_query_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_m_755_, v_query_756_);
lean_dec_ref(v_query_756_);
lean_dec_ref(v_m_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_m_758_, v_a_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_value_761_; lean_object* v___x_762_; 
v_value_761_ = lean_ctor_get(v___x_760_, 2);
lean_inc(v_value_761_);
lean_dec_ref_known(v___x_760_, 3);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_value_761_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = lean_box(0);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_764_, v_a_765_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_m_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_767_, lean_object* v___y_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_768_);
v___x_775_ = lean_apply_7(v_k_767_, v_b_769_, v___y_768_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_776_, lean_object* v___y_777_, lean_object* v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_776_, v___y_777_, v_b_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_777_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_785_, uint8_t v_bi_786_, lean_object* v_type_787_, lean_object* v_k_788_, uint8_t v_kind_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___f_796_; lean_object* v___x_797_; 
lean_inc(v___y_790_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_796_, 0, v_k_788_);
lean_closure_set(v___f_796_, 1, v___y_790_);
v___x_797_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_785_, v_bi_786_, v_type_787_, v___f_796_, v_kind_789_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
return v___x_797_;
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_806_, lean_object* v_bi_807_, lean_object* v_type_808_, lean_object* v_k_809_, lean_object* v_kind_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_bi_boxed_817_; uint8_t v_kind_boxed_818_; lean_object* v_res_819_; 
v_bi_boxed_817_ = lean_unbox(v_bi_807_);
v_kind_boxed_818_ = lean_unbox(v_kind_810_);
v_res_819_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_806_, v_bi_boxed_817_, v_type_808_, v_k_809_, v_kind_boxed_818_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_820_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_834_, lean_object* v_type_835_, lean_object* v_val_836_, lean_object* v_k_837_, uint8_t v_nondep_838_, uint8_t v_kind_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___f_846_; lean_object* v___x_847_; 
lean_inc(v___y_840_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_846_, 0, v_k_837_);
lean_closure_set(v___f_846_, 1, v___y_840_);
v___x_847_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_834_, v_type_835_, v_val_836_, v___f_846_, v_nondep_838_, v_kind_839_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_847_) == 0)
{
return v___x_847_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_856_, lean_object* v_type_857_, lean_object* v_val_858_, lean_object* v_k_859_, lean_object* v_nondep_860_, lean_object* v_kind_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v_nondep_boxed_868_; uint8_t v_kind_boxed_869_; lean_object* v_res_870_; 
v_nondep_boxed_868_ = lean_unbox(v_nondep_860_);
v_kind_boxed_869_ = lean_unbox(v_kind_861_);
v_res_870_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_856_, v_type_857_, v_val_858_, v_k_859_, v_nondep_boxed_868_, v_kind_boxed_869_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_874_, lean_object* v_pre_875_, lean_object* v_post_876_, uint8_t v_usedLetOnly_877_, uint8_t v_skipConstInApp_878_, uint8_t v_skipInstances_879_, lean_object* v_body_880_, lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_array_push(v_fvars_874_, v_x_881_);
v___x_889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_875_, v_post_876_, v_usedLetOnly_877_, v_skipConstInApp_878_, v_skipInstances_879_, v___x_888_, v_body_880_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_890_, lean_object* v_pre_891_, lean_object* v_post_892_, lean_object* v_usedLetOnly_893_, lean_object* v_skipConstInApp_894_, lean_object* v_skipInstances_895_, lean_object* v_body_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v_usedLetOnly_boxed_904_; uint8_t v_skipConstInApp_boxed_905_; uint8_t v_skipInstances_boxed_906_; lean_object* v_res_907_; 
v_usedLetOnly_boxed_904_ = lean_unbox(v_usedLetOnly_893_);
v_skipConstInApp_boxed_905_ = lean_unbox(v_skipConstInApp_894_);
v_skipInstances_boxed_906_ = lean_unbox(v_skipInstances_895_);
v_res_907_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_890_, v_pre_891_, v_post_892_, v_usedLetOnly_boxed_904_, v_skipConstInApp_boxed_905_, v_skipInstances_boxed_906_, v_body_896_, v_x_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_908_, lean_object* v_post_909_, uint8_t v_usedLetOnly_910_, uint8_t v_skipConstInApp_911_, uint8_t v_skipInstances_912_, lean_object* v_e_913_, lean_object* v_a_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
lean_inc_ref(v_post_909_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc_ref(v_e_913_);
v___x_920_ = lean_apply_6(v_post_909_, v_e_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_939_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_939_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
switch(lean_obj_tag(v_a_921_))
{
case 0:
{
lean_object* v_e_925_; lean_object* v___x_927_; 
lean_dec_ref(v_e_913_);
lean_dec_ref(v_post_909_);
lean_dec_ref(v_pre_908_);
v_e_925_ = lean_ctor_get(v_a_921_, 0);
lean_inc_ref(v_e_925_);
lean_dec_ref_known(v_a_921_, 1);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_e_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_e_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
case 1:
{
lean_object* v_e_929_; lean_object* v___x_930_; 
lean_del_object(v___x_923_);
lean_dec_ref(v_e_913_);
v_e_929_ = lean_ctor_get(v_a_921_, 0);
lean_inc_ref(v_e_929_);
lean_dec_ref_known(v_a_921_, 1);
v___x_930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_908_, v_post_909_, v_usedLetOnly_910_, v_skipConstInApp_911_, v_skipInstances_912_, v_e_929_, v_a_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_930_;
}
default: 
{
lean_object* v_e_x3f_931_; 
lean_dec_ref(v_post_909_);
lean_dec_ref(v_pre_908_);
v_e_x3f_931_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_e_x3f_931_);
lean_dec_ref_known(v_a_921_, 1);
if (lean_obj_tag(v_e_x3f_931_) == 0)
{
lean_object* v___x_933_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_e_913_);
v___x_933_ = v___x_923_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_e_913_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; 
lean_dec_ref(v_e_913_);
v_val_935_ = lean_ctor_get(v_e_x3f_931_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_e_x3f_931_, 1);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_val_935_);
v___x_937_ = v___x_923_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_val_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_e_913_);
lean_dec_ref(v_post_909_);
lean_dec_ref(v_pre_908_);
v_a_940_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_920_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_920_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_948_, lean_object* v_post_949_, uint8_t v_usedLetOnly_950_, uint8_t v_skipConstInApp_951_, uint8_t v_skipInstances_952_, lean_object* v_fvars_953_, lean_object* v_e_954_, lean_object* v_a_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
if (lean_obj_tag(v_e_954_) == 6)
{
lean_object* v_binderName_961_; lean_object* v_binderType_962_; lean_object* v_body_963_; uint8_t v_binderInfo_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_binderName_961_ = lean_ctor_get(v_e_954_, 0);
lean_inc(v_binderName_961_);
v_binderType_962_ = lean_ctor_get(v_e_954_, 1);
lean_inc_ref(v_binderType_962_);
v_body_963_ = lean_ctor_get(v_e_954_, 2);
lean_inc_ref(v_body_963_);
v_binderInfo_964_ = lean_ctor_get_uint8(v_e_954_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_954_, 3);
v___x_965_ = lean_expr_instantiate_rev(v_binderType_962_, v_fvars_953_);
lean_dec_ref(v_binderType_962_);
lean_inc_ref(v_post_949_);
lean_inc_ref(v_pre_948_);
v___x_966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_948_, v_post_949_, v_usedLetOnly_950_, v_skipConstInApp_951_, v_skipInstances_952_, v___x_965_, v_a_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___f_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_box(v_usedLetOnly_950_);
v___x_969_ = lean_box(v_skipConstInApp_951_);
v___x_970_ = lean_box(v_skipInstances_952_);
v___f_971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_971_, 0, v_fvars_953_);
lean_closure_set(v___f_971_, 1, v_pre_948_);
lean_closure_set(v___f_971_, 2, v_post_949_);
lean_closure_set(v___f_971_, 3, v___x_968_);
lean_closure_set(v___f_971_, 4, v___x_969_);
lean_closure_set(v___f_971_, 5, v___x_970_);
lean_closure_set(v___f_971_, 6, v_body_963_);
v___x_972_ = 0;
v___x_973_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_961_, v_binderInfo_964_, v_a_967_, v___f_971_, v___x_972_, v_a_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_973_;
}
else
{
lean_dec_ref(v_body_963_);
lean_dec(v_binderName_961_);
lean_dec_ref(v_fvars_953_);
lean_dec_ref(v_post_949_);
lean_dec_ref(v_pre_948_);
return v___x_966_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_expr_instantiate_rev(v_e_954_, v_fvars_953_);
lean_dec_ref(v_e_954_);
lean_inc_ref(v_post_949_);
lean_inc_ref(v_pre_948_);
v___x_975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_948_, v_post_949_, v_usedLetOnly_950_, v_skipConstInApp_951_, v_skipInstances_952_, v___x_974_, v_a_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; uint8_t v___x_977_; uint8_t v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = 0;
v___x_978_ = 1;
v___x_979_ = 1;
v___x_980_ = l_Lean_Meta_mkLambdaFVars(v_fvars_953_, v_a_976_, v___x_977_, v_usedLetOnly_950_, v___x_977_, v___x_978_, v___x_979_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec_ref(v_fvars_953_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_948_, v_post_949_, v_usedLetOnly_950_, v_skipConstInApp_951_, v_skipInstances_952_, v_a_981_, v_a_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_982_;
}
else
{
lean_dec_ref(v_post_949_);
lean_dec_ref(v_pre_948_);
return v___x_980_;
}
}
else
{
lean_dec_ref(v_fvars_953_);
lean_dec_ref(v_post_949_);
lean_dec_ref(v_pre_948_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_983_, lean_object* v_pre_984_, lean_object* v_post_985_, uint8_t v_usedLetOnly_986_, uint8_t v_skipConstInApp_987_, uint8_t v_skipInstances_988_, lean_object* v_body_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_array_push(v_fvars_983_, v_x_990_);
v___x_998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_984_, v_post_985_, v_usedLetOnly_986_, v_skipConstInApp_987_, v_skipInstances_988_, v___x_997_, v_body_989_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_999_, lean_object* v_pre_1000_, lean_object* v_post_1001_, lean_object* v_usedLetOnly_1002_, lean_object* v_skipConstInApp_1003_, lean_object* v_skipInstances_1004_, lean_object* v_body_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v_usedLetOnly_boxed_1013_; uint8_t v_skipConstInApp_boxed_1014_; uint8_t v_skipInstances_boxed_1015_; lean_object* v_res_1016_; 
v_usedLetOnly_boxed_1013_ = lean_unbox(v_usedLetOnly_1002_);
v_skipConstInApp_boxed_1014_ = lean_unbox(v_skipConstInApp_1003_);
v_skipInstances_boxed_1015_ = lean_unbox(v_skipInstances_1004_);
v_res_1016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_999_, v_pre_1000_, v_post_1001_, v_usedLetOnly_boxed_1013_, v_skipConstInApp_boxed_1014_, v_skipInstances_boxed_1015_, v_body_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_1017_, lean_object* v_post_1018_, uint8_t v_usedLetOnly_1019_, uint8_t v_skipConstInApp_1020_, uint8_t v_skipInstances_1021_, lean_object* v_fvars_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
if (lean_obj_tag(v_e_1023_) == 8)
{
lean_object* v_declName_1030_; lean_object* v_type_1031_; lean_object* v_value_1032_; lean_object* v_body_1033_; uint8_t v_nondep_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_declName_1030_ = lean_ctor_get(v_e_1023_, 0);
lean_inc(v_declName_1030_);
v_type_1031_ = lean_ctor_get(v_e_1023_, 1);
lean_inc_ref(v_type_1031_);
v_value_1032_ = lean_ctor_get(v_e_1023_, 2);
lean_inc_ref(v_value_1032_);
v_body_1033_ = lean_ctor_get(v_e_1023_, 3);
lean_inc_ref(v_body_1033_);
v_nondep_1034_ = lean_ctor_get_uint8(v_e_1023_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1023_, 4);
v___x_1035_ = lean_expr_instantiate_rev(v_type_1031_, v_fvars_1022_);
lean_dec_ref(v_type_1031_);
lean_inc_ref(v_post_1018_);
lean_inc_ref(v_pre_1017_);
v___x_1036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1017_, v_post_1018_, v_usedLetOnly_1019_, v_skipConstInApp_1020_, v_skipInstances_1021_, v___x_1035_, v_a_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = lean_expr_instantiate_rev(v_value_1032_, v_fvars_1022_);
lean_dec_ref(v_value_1032_);
lean_inc_ref(v_post_1018_);
lean_inc_ref(v_pre_1017_);
v___x_1039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1017_, v_post_1018_, v_usedLetOnly_1019_, v_skipConstInApp_1020_, v_skipInstances_1021_, v___x_1038_, v_a_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___f_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = lean_box(v_usedLetOnly_1019_);
v___x_1042_ = lean_box(v_skipConstInApp_1020_);
v___x_1043_ = lean_box(v_skipInstances_1021_);
v___f_1044_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1044_, 0, v_fvars_1022_);
lean_closure_set(v___f_1044_, 1, v_pre_1017_);
lean_closure_set(v___f_1044_, 2, v_post_1018_);
lean_closure_set(v___f_1044_, 3, v___x_1041_);
lean_closure_set(v___f_1044_, 4, v___x_1042_);
lean_closure_set(v___f_1044_, 5, v___x_1043_);
lean_closure_set(v___f_1044_, 6, v_body_1033_);
v___x_1045_ = 0;
v___x_1046_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_1030_, v_a_1037_, v_a_1040_, v___f_1044_, v_nondep_1034_, v___x_1045_, v_a_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1046_;
}
else
{
lean_dec(v_a_1037_);
lean_dec_ref(v_body_1033_);
lean_dec(v_declName_1030_);
lean_dec_ref(v_fvars_1022_);
lean_dec_ref(v_post_1018_);
lean_dec_ref(v_pre_1017_);
return v___x_1039_;
}
}
else
{
lean_dec_ref(v_body_1033_);
lean_dec_ref(v_value_1032_);
lean_dec(v_declName_1030_);
lean_dec_ref(v_fvars_1022_);
lean_dec_ref(v_post_1018_);
lean_dec_ref(v_pre_1017_);
return v___x_1036_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_expr_instantiate_rev(v_e_1023_, v_fvars_1022_);
lean_dec_ref(v_e_1023_);
lean_inc_ref(v_post_1018_);
lean_inc_ref(v_pre_1017_);
v___x_1048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1017_, v_post_1018_, v_usedLetOnly_1019_, v_skipConstInApp_1020_, v_skipInstances_1021_, v___x_1047_, v_a_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = 0;
v___x_1051_ = 1;
v___x_1052_ = l_Lean_Meta_mkLetFVars(v_fvars_1022_, v_a_1049_, v_usedLetOnly_1019_, v___x_1050_, v___x_1051_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec_ref(v_fvars_1022_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1017_, v_post_1018_, v_usedLetOnly_1019_, v_skipConstInApp_1020_, v_skipInstances_1021_, v_a_1053_, v_a_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1054_;
}
else
{
lean_dec_ref(v_post_1018_);
lean_dec_ref(v_pre_1017_);
return v___x_1052_;
}
}
else
{
lean_dec_ref(v_fvars_1022_);
lean_dec_ref(v_post_1018_);
lean_dec_ref(v_pre_1017_);
return v___x_1048_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1055_; lean_object* v_dummy_1056_; 
v___x_1055_ = lean_box(0);
v_dummy_1056_ = l_Lean_Expr_sort___override(v___x_1055_);
return v_dummy_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_1057_, lean_object* v_post_1058_, uint8_t v_usedLetOnly_1059_, uint8_t v_skipConstInApp_1060_, uint8_t v_skipInstances_1061_, size_t v_sz_1062_, size_t v_i_1063_, lean_object* v_bs_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_lt(v_i_1063_, v_sz_1062_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref(v_post_1058_);
lean_dec_ref(v_pre_1057_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_bs_1064_);
return v___x_1072_;
}
else
{
lean_object* v_v_1073_; lean_object* v___x_1074_; 
v_v_1073_ = lean_array_uget_borrowed(v_bs_1064_, v_i_1063_);
lean_inc(v_v_1073_);
lean_inc_ref(v_post_1058_);
lean_inc_ref(v_pre_1057_);
v___x_1074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1057_, v_post_1058_, v_usedLetOnly_1059_, v_skipConstInApp_1060_, v_skipInstances_1061_, v_v_1073_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v_bs_x27_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = lean_unsigned_to_nat(0u);
v_bs_x27_1077_ = lean_array_uset(v_bs_1064_, v_i_1063_, v___x_1076_);
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_add(v_i_1063_, v___x_1078_);
v___x_1080_ = lean_array_uset(v_bs_x27_1077_, v_i_1063_, v_a_1075_);
v_i_1063_ = v___x_1079_;
v_bs_1064_ = v___x_1080_;
goto _start;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_bs_1064_);
lean_dec_ref(v_post_1058_);
lean_dec_ref(v_pre_1057_);
v_a_1082_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1074_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1074_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1090_, lean_object* v_post_1091_, uint8_t v_usedLetOnly_1092_, uint8_t v_skipConstInApp_1093_, uint8_t v_skipInstances_1094_, lean_object* v___x_1095_, lean_object* v___y_1096_, lean_object* v_b_1097_, lean_object* v_a_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1090_, v_post_1091_, v_usedLetOnly_1092_, v_skipConstInApp_1093_, v_skipInstances_1094_, v___x_1095_, v___y_1096_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = lean_array_fset(v_b_1097_, v_a_1098_, v_a_1105_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1110_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_b_1097_);
v_a_1115_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1104_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1104_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1123_, lean_object* v_post_1124_, lean_object* v_usedLetOnly_1125_, lean_object* v_skipConstInApp_1126_, lean_object* v_skipInstances_1127_, lean_object* v___x_1128_, lean_object* v___y_1129_, lean_object* v_b_1130_, lean_object* v_a_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_usedLetOnly_boxed_1137_; uint8_t v_skipConstInApp_boxed_1138_; uint8_t v_skipInstances_boxed_1139_; lean_object* v_res_1140_; 
v_usedLetOnly_boxed_1137_ = lean_unbox(v_usedLetOnly_1125_);
v_skipConstInApp_boxed_1138_ = lean_unbox(v_skipConstInApp_1126_);
v_skipInstances_boxed_1139_ = lean_unbox(v_skipInstances_1127_);
v_res_1140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1123_, v_post_1124_, v_usedLetOnly_boxed_1137_, v_skipConstInApp_boxed_1138_, v_skipInstances_boxed_1139_, v___x_1128_, v___y_1129_, v_b_1130_, v_a_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_a_1131_);
lean_dec(v___y_1129_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1141_, lean_object* v___x_1142_, lean_object* v_pre_1143_, lean_object* v_post_1144_, uint8_t v_usedLetOnly_1145_, uint8_t v_skipConstInApp_1146_, uint8_t v_skipInstances_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___y_1157_; uint8_t v___x_1180_; 
v___x_1180_ = lean_nat_dec_lt(v_a_1148_, v_upperBound_1141_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec(v_a_1148_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_b_1149_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = lean_array_fget_borrowed(v_b_1149_, v_a_1148_);
v___x_1183_ = lean_array_get_size(v___x_1142_);
v___x_1184_ = lean_nat_dec_lt(v_a_1148_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___f_1188_; 
lean_inc(v___x_1182_);
v___x_1185_ = lean_box(v_usedLetOnly_1145_);
v___x_1186_ = lean_box(v_skipConstInApp_1146_);
v___x_1187_ = lean_box(v_skipInstances_1147_);
lean_inc(v_a_1148_);
lean_inc(v___y_1150_);
lean_inc_ref(v_post_1144_);
lean_inc_ref(v_pre_1143_);
v___f_1188_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1188_, 0, v_pre_1143_);
lean_closure_set(v___f_1188_, 1, v_post_1144_);
lean_closure_set(v___f_1188_, 2, v___x_1185_);
lean_closure_set(v___f_1188_, 3, v___x_1186_);
lean_closure_set(v___f_1188_, 4, v___x_1187_);
lean_closure_set(v___f_1188_, 5, v___x_1182_);
lean_closure_set(v___f_1188_, 6, v___y_1150_);
lean_closure_set(v___f_1188_, 7, v_b_1149_);
lean_closure_set(v___f_1188_, 8, v_a_1148_);
v___y_1157_ = v___f_1188_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1189_; uint8_t v_isInstance_1190_; 
v___x_1189_ = lean_array_fget_borrowed(v___x_1142_, v_a_1148_);
v_isInstance_1190_ = lean_ctor_get_uint8(v___x_1189_, sizeof(void*)*1 + 4);
if (v_isInstance_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; 
lean_inc(v___x_1182_);
v___x_1191_ = lean_box(v_usedLetOnly_1145_);
v___x_1192_ = lean_box(v_skipConstInApp_1146_);
v___x_1193_ = lean_box(v_skipInstances_1147_);
lean_inc(v_a_1148_);
lean_inc(v___y_1150_);
lean_inc_ref(v_post_1144_);
lean_inc_ref(v_pre_1143_);
v___f_1194_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1194_, 0, v_pre_1143_);
lean_closure_set(v___f_1194_, 1, v_post_1144_);
lean_closure_set(v___f_1194_, 2, v___x_1191_);
lean_closure_set(v___f_1194_, 3, v___x_1192_);
lean_closure_set(v___f_1194_, 4, v___x_1193_);
lean_closure_set(v___f_1194_, 5, v___x_1182_);
lean_closure_set(v___f_1194_, 6, v___y_1150_);
lean_closure_set(v___f_1194_, 7, v_b_1149_);
lean_closure_set(v___f_1194_, 8, v_a_1148_);
v___y_1157_ = v___f_1194_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1195_; lean_object* v___f_1196_; 
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1149_);
v___f_1196_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1196_, 0, v___x_1195_);
v___y_1157_ = v___f_1196_;
goto v___jp_1156_;
}
}
}
v___jp_1156_:
{
lean_object* v___x_1158_; 
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
v___x_1158_ = lean_apply_5(v___y_1157_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1171_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1171_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1171_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
if (lean_obj_tag(v_a_1159_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1148_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
v_a_1163_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v_a_1159_, 1);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v_a_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_del_object(v___x_1161_);
v_a_1167_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v_a_1159_, 1);
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_add(v_a_1148_, v___x_1168_);
lean_dec(v_a_1148_);
v_a_1148_ = v___x_1169_;
v_b_1149_ = v_a_1167_;
goto _start;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1148_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
v_a_1172_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1158_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1158_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1197_, lean_object* v_pre_1198_, lean_object* v_post_1199_, uint8_t v_usedLetOnly_1200_, uint8_t v_skipConstInApp_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_f_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; 
if (lean_obj_tag(v_x_1202_) == 5)
{
lean_object* v_fn_1260_; lean_object* v_arg_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_fn_1260_ = lean_ctor_get(v_x_1202_, 0);
lean_inc_ref(v_fn_1260_);
v_arg_1261_ = lean_ctor_get(v_x_1202_, 1);
lean_inc_ref(v_arg_1261_);
lean_dec_ref_known(v_x_1202_, 2);
v___x_1262_ = lean_array_set(v_x_1203_, v_x_1204_, v_arg_1261_);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_sub(v_x_1204_, v___x_1263_);
lean_dec(v_x_1204_);
v_x_1202_ = v_fn_1260_;
v_x_1203_ = v___x_1262_;
v_x_1204_ = v___x_1264_;
goto _start;
}
else
{
lean_dec(v_x_1204_);
if (v_skipConstInApp_1201_ == 0)
{
goto v___jp_1257_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Lean_Expr_isConst(v_x_1202_);
if (v___x_1266_ == 0)
{
goto v___jp_1257_;
}
else
{
v_f_1212_ = v_x_1202_;
v___y_1213_ = v___y_1205_;
v___y_1214_ = v___y_1206_;
v___y_1215_ = v___y_1207_;
v___y_1216_ = v___y_1208_;
v___y_1217_ = v___y_1209_;
goto v___jp_1211_;
}
}
}
v___jp_1211_:
{
if (v_skipInstances_1197_ == 0)
{
size_t v_sz_1218_; size_t v___x_1219_; lean_object* v___x_1220_; 
v_sz_1218_ = lean_array_size(v_x_1203_);
v___x_1219_ = ((size_t)0ULL);
lean_inc_ref(v_post_1199_);
lean_inc_ref(v_pre_1198_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1198_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1197_, v_sz_1218_, v___x_1219_, v_x_1203_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = l_Lean_mkAppN(v_f_1212_, v_a_1221_);
lean_dec(v_a_1221_);
v___x_1223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1198_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1197_, v___x_1222_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1223_;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v_f_1212_);
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_pre_1198_);
v_a_1224_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1220_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1220_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_array_get_size(v_x_1203_);
lean_inc_ref(v_f_1212_);
v___x_1233_ = l_Lean_Meta_getFunInfoNArgs(v_f_1212_, v___x_1232_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_paramInfo_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v_paramInfo_1235_ = lean_ctor_get(v_a_1234_, 0);
lean_inc_ref(v_paramInfo_1235_);
lean_dec(v_a_1234_);
v___x_1236_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1199_);
lean_inc_ref(v_pre_1198_);
v___x_1237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1232_, v_paramInfo_1235_, v_pre_1198_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1197_, v___x_1236_, v_x_1203_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec_ref(v_paramInfo_1235_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = l_Lean_mkAppN(v_f_1212_, v_a_1238_);
lean_dec(v_a_1238_);
v___x_1240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1198_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1197_, v___x_1239_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1240_;
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_f_1212_);
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_pre_1198_);
v_a_1241_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1237_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1237_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v_f_1212_);
lean_dec_ref(v_x_1203_);
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_pre_1198_);
v_a_1249_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1233_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1233_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; 
lean_inc_ref(v_post_1199_);
lean_inc_ref(v_pre_1198_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1198_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1197_, v_x_1202_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v_f_1212_ = v_a_1259_;
v___y_1213_ = v___y_1205_;
v___y_1214_ = v___y_1206_;
v___y_1215_ = v___y_1207_;
v___y_1216_ = v___y_1208_;
v___y_1217_ = v___y_1209_;
goto v___jp_1211_;
}
else
{
lean_dec_ref(v_x_1203_);
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_pre_1198_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1267_, lean_object* v_pre_1268_, lean_object* v_e_1269_, lean_object* v_post_1270_, uint8_t v_usedLetOnly_1271_, uint8_t v_skipConstInApp_1272_, uint8_t v_skipInstances_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Core_checkSystem(v___x_1267_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1280_, 1);
lean_inc_ref(v_pre_1268_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc_ref(v_e_1269_);
v___x_1281_ = lean_apply_6(v_pre_1268_, v_e_1269_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, lean_box(0));
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1330_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1330_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1330_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___y_1287_; 
switch(lean_obj_tag(v_a_1282_))
{
case 0:
{
lean_object* v_e_1322_; lean_object* v___x_1324_; 
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_pre_1268_);
v_e_1322_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_e_1322_);
lean_dec_ref_known(v_a_1282_, 1);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_e_1322_);
v___x_1324_ = v___x_1284_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_e_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
case 1:
{
lean_object* v_e_1326_; lean_object* v___x_1327_; 
lean_del_object(v___x_1284_);
lean_dec_ref(v_e_1269_);
v_e_1326_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_e_1326_);
lean_dec_ref_known(v_a_1282_, 1);
v___x_1327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_e_1326_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1327_;
}
default: 
{
lean_object* v_e_x3f_1328_; 
lean_del_object(v___x_1284_);
v_e_x3f_1328_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_e_x3f_1328_);
lean_dec_ref_known(v_a_1282_, 1);
if (lean_obj_tag(v_e_x3f_1328_) == 0)
{
v___y_1287_ = v_e_1269_;
goto v___jp_1286_;
}
else
{
lean_object* v_val_1329_; 
lean_dec_ref(v_e_1269_);
v_val_1329_ = lean_ctor_get(v_e_x3f_1328_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v_e_x3f_1328_, 1);
v___y_1287_ = v_val_1329_;
goto v___jp_1286_;
}
}
}
v___jp_1286_:
{
switch(lean_obj_tag(v___y_1287_))
{
case 7:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___x_1288_, v___y_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1289_;
}
case 6:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___x_1290_, v___y_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1291_;
}
case 8:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1293_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___x_1292_, v___y_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1293_;
}
case 5:
{
lean_object* v_dummy_1294_; lean_object* v_nargs_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_dummy_1294_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1295_ = l_Lean_Expr_getAppNumArgs(v___y_1287_);
lean_inc(v_nargs_1295_);
v___x_1296_ = lean_mk_array(v_nargs_1295_, v_dummy_1294_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_sub(v_nargs_1295_, v___x_1297_);
lean_dec(v_nargs_1295_);
v___x_1299_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1273_, v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v___y_1287_, v___x_1296_, v___x_1298_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1299_;
}
case 10:
{
lean_object* v_data_1300_; lean_object* v_expr_1301_; lean_object* v___x_1302_; 
v_data_1300_ = lean_ctor_get(v___y_1287_, 0);
v_expr_1301_ = lean_ctor_get(v___y_1287_, 1);
lean_inc_ref(v_expr_1301_);
lean_inc_ref(v_post_1270_);
lean_inc_ref(v_pre_1268_);
v___x_1302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_expr_1301_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; size_t v___x_1304_; size_t v___x_1305_; uint8_t v___x_1306_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = lean_ptr_addr(v_expr_1301_);
v___x_1305_ = lean_ptr_addr(v_a_1303_);
v___x_1306_ = lean_usize_dec_eq(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_inc(v_data_1300_);
lean_dec_ref_known(v___y_1287_, 2);
v___x_1307_ = l_Lean_Expr_mdata___override(v_data_1300_, v_a_1303_);
v___x_1308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___x_1307_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; 
lean_dec(v_a_1303_);
v___x_1309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___y_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1309_;
}
}
else
{
lean_dec_ref_known(v___y_1287_, 2);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_pre_1268_);
return v___x_1302_;
}
}
case 11:
{
lean_object* v_typeName_1310_; lean_object* v_idx_1311_; lean_object* v_struct_1312_; lean_object* v___x_1313_; 
v_typeName_1310_ = lean_ctor_get(v___y_1287_, 0);
v_idx_1311_ = lean_ctor_get(v___y_1287_, 1);
v_struct_1312_ = lean_ctor_get(v___y_1287_, 2);
lean_inc_ref(v_struct_1312_);
lean_inc_ref(v_post_1270_);
lean_inc_ref(v_pre_1268_);
v___x_1313_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v_struct_1312_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; size_t v___x_1315_; size_t v___x_1316_; uint8_t v___x_1317_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1315_ = lean_ptr_addr(v_struct_1312_);
v___x_1316_ = lean_ptr_addr(v_a_1314_);
v___x_1317_ = lean_usize_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_inc(v_idx_1311_);
lean_inc(v_typeName_1310_);
lean_dec_ref_known(v___y_1287_, 3);
v___x_1318_ = l_Lean_Expr_proj___override(v_typeName_1310_, v_idx_1311_, v_a_1314_);
v___x_1319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___x_1318_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_dec(v_a_1314_);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___y_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1320_;
}
}
else
{
lean_dec_ref_known(v___y_1287_, 3);
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_pre_1268_);
return v___x_1313_;
}
}
default: 
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1268_, v_post_1270_, v_usedLetOnly_1271_, v_skipConstInApp_1272_, v_skipInstances_1273_, v___y_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_pre_1268_);
v_a_1331_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1281_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1281_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v_post_1270_);
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_pre_1268_);
v_a_1339_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1280_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1280_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1347_, lean_object* v_pre_1348_, lean_object* v_e_1349_, lean_object* v_post_1350_, lean_object* v_usedLetOnly_1351_, lean_object* v_skipConstInApp_1352_, lean_object* v_skipInstances_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_usedLetOnly_boxed_1360_; uint8_t v_skipConstInApp_boxed_1361_; uint8_t v_skipInstances_boxed_1362_; lean_object* v_res_1363_; 
v_usedLetOnly_boxed_1360_ = lean_unbox(v_usedLetOnly_1351_);
v_skipConstInApp_boxed_1361_ = lean_unbox(v_skipConstInApp_1352_);
v_skipInstances_boxed_1362_ = lean_unbox(v_skipInstances_1353_);
v_res_1363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1347_, v_pre_1348_, v_e_1349_, v_post_1350_, v_usedLetOnly_boxed_1360_, v_skipConstInApp_boxed_1361_, v_skipInstances_boxed_1362_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1364_, lean_object* v_post_1365_, uint8_t v_usedLetOnly_1366_, uint8_t v_skipConstInApp_1367_, uint8_t v_skipInstances_1368_, lean_object* v_e_1369_, lean_object* v_a_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_inc(v_a_1370_);
v___x_1376_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1376_, 0, lean_box(0));
lean_closure_set(v___x_1376_, 1, lean_box(0));
lean_closure_set(v___x_1376_, 2, v_a_1370_);
v___x_1377_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1376_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1412_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1412_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1412_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1378_, v_e_1369_);
lean_dec(v_a_1378_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; 
lean_del_object(v___x_1380_);
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1384_ = lean_box(v_usedLetOnly_1366_);
v___x_1385_ = lean_box(v_skipConstInApp_1367_);
v___x_1386_ = lean_box(v_skipInstances_1368_);
lean_inc_ref(v_e_1369_);
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1387_, 0, v___x_1383_);
lean_closure_set(v___f_1387_, 1, v_pre_1364_);
lean_closure_set(v___f_1387_, 2, v_e_1369_);
lean_closure_set(v___f_1387_, 3, v_post_1365_);
lean_closure_set(v___f_1387_, 4, v___x_1384_);
lean_closure_set(v___f_1387_, 5, v___x_1385_);
lean_closure_set(v___f_1387_, 6, v___x_1386_);
v___x_1388_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1387_, v_a_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc_n(v_a_1389_, 2);
lean_dec_ref_known(v___x_1388_, 1);
lean_inc(v_a_1370_);
v___f_1390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1390_, 0, v_a_1370_);
lean_closure_set(v___f_1390_, 1, v_e_1369_);
lean_closure_set(v___f_1390_, 2, v_a_1389_);
v___x_1391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1390_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1391_, 0);
lean_dec(v_unused_1399_);
v___x_1393_ = v___x_1391_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___x_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_a_1389_);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1389_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1389_);
v_a_1400_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1391_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1391_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_dec_ref(v_e_1369_);
return v___x_1388_;
}
}
else
{
lean_object* v_val_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_e_1369_);
lean_dec_ref(v_post_1365_);
lean_dec_ref(v_pre_1364_);
v_val_1408_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1382_, 1);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v_val_1408_);
v___x_1410_ = v___x_1380_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_val_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_e_1369_);
lean_dec_ref(v_post_1365_);
lean_dec_ref(v_pre_1364_);
v_a_1413_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1377_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1377_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1421_, lean_object* v_pre_1422_, lean_object* v_post_1423_, lean_object* v_usedLetOnly_1424_, lean_object* v_skipConstInApp_1425_, lean_object* v_skipInstances_1426_, lean_object* v_body_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v_usedLetOnly_boxed_1435_; uint8_t v_skipConstInApp_boxed_1436_; uint8_t v_skipInstances_boxed_1437_; lean_object* v_res_1438_; 
v_usedLetOnly_boxed_1435_ = lean_unbox(v_usedLetOnly_1424_);
v_skipConstInApp_boxed_1436_ = lean_unbox(v_skipConstInApp_1425_);
v_skipInstances_boxed_1437_ = lean_unbox(v_skipInstances_1426_);
v_res_1438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1421_, v_pre_1422_, v_post_1423_, v_usedLetOnly_boxed_1435_, v_skipConstInApp_boxed_1436_, v_skipInstances_boxed_1437_, v_body_1427_, v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1439_, lean_object* v_post_1440_, uint8_t v_usedLetOnly_1441_, uint8_t v_skipConstInApp_1442_, uint8_t v_skipInstances_1443_, lean_object* v_fvars_1444_, lean_object* v_e_1445_, lean_object* v_a_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
if (lean_obj_tag(v_e_1445_) == 7)
{
lean_object* v_binderName_1452_; lean_object* v_binderType_1453_; lean_object* v_body_1454_; uint8_t v_binderInfo_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_binderName_1452_ = lean_ctor_get(v_e_1445_, 0);
lean_inc(v_binderName_1452_);
v_binderType_1453_ = lean_ctor_get(v_e_1445_, 1);
lean_inc_ref(v_binderType_1453_);
v_body_1454_ = lean_ctor_get(v_e_1445_, 2);
lean_inc_ref(v_body_1454_);
v_binderInfo_1455_ = lean_ctor_get_uint8(v_e_1445_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1445_, 3);
v___x_1456_ = lean_expr_instantiate_rev(v_binderType_1453_, v_fvars_1444_);
lean_dec_ref(v_binderType_1453_);
lean_inc_ref(v_post_1440_);
lean_inc_ref(v_pre_1439_);
v___x_1457_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v___x_1456_, v_a_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___f_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = lean_box(v_usedLetOnly_1441_);
v___x_1460_ = lean_box(v_skipConstInApp_1442_);
v___x_1461_ = lean_box(v_skipInstances_1443_);
v___f_1462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1462_, 0, v_fvars_1444_);
lean_closure_set(v___f_1462_, 1, v_pre_1439_);
lean_closure_set(v___f_1462_, 2, v_post_1440_);
lean_closure_set(v___f_1462_, 3, v___x_1459_);
lean_closure_set(v___f_1462_, 4, v___x_1460_);
lean_closure_set(v___f_1462_, 5, v___x_1461_);
lean_closure_set(v___f_1462_, 6, v_body_1454_);
v___x_1463_ = 0;
v___x_1464_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1452_, v_binderInfo_1455_, v_a_1458_, v___f_1462_, v___x_1463_, v_a_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1464_;
}
else
{
lean_dec_ref(v_body_1454_);
lean_dec(v_binderName_1452_);
lean_dec_ref(v_fvars_1444_);
lean_dec_ref(v_post_1440_);
lean_dec_ref(v_pre_1439_);
return v___x_1457_;
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_expr_instantiate_rev(v_e_1445_, v_fvars_1444_);
lean_dec_ref(v_e_1445_);
lean_inc_ref(v_post_1440_);
lean_inc_ref(v_pre_1439_);
v___x_1466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v___x_1465_, v_a_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; uint8_t v___x_1468_; uint8_t v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = 0;
v___x_1469_ = 1;
v___x_1470_ = 1;
v___x_1471_ = l_Lean_Meta_mkForallFVars(v_fvars_1444_, v_a_1467_, v___x_1468_, v_usedLetOnly_1441_, v___x_1469_, v___x_1470_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_fvars_1444_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v_a_1472_, v_a_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1473_;
}
else
{
lean_dec_ref(v_post_1440_);
lean_dec_ref(v_pre_1439_);
return v___x_1471_;
}
}
else
{
lean_dec_ref(v_fvars_1444_);
lean_dec_ref(v_post_1440_);
lean_dec_ref(v_pre_1439_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1474_, lean_object* v_pre_1475_, lean_object* v_post_1476_, uint8_t v_usedLetOnly_1477_, uint8_t v_skipConstInApp_1478_, uint8_t v_skipInstances_1479_, lean_object* v_body_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_array_push(v_fvars_1474_, v_x_1481_);
v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1475_, v_post_1476_, v_usedLetOnly_1477_, v_skipConstInApp_1478_, v_skipInstances_1479_, v___x_1488_, v_body_1480_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1490_, lean_object* v_post_1491_, lean_object* v_usedLetOnly_1492_, lean_object* v_skipConstInApp_1493_, lean_object* v_skipInstances_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_usedLetOnly_boxed_1502_; uint8_t v_skipConstInApp_boxed_1503_; uint8_t v_skipInstances_boxed_1504_; lean_object* v_res_1505_; 
v_usedLetOnly_boxed_1502_ = lean_unbox(v_usedLetOnly_1492_);
v_skipConstInApp_boxed_1503_ = lean_unbox(v_skipConstInApp_1493_);
v_skipInstances_boxed_1504_ = lean_unbox(v_skipInstances_1494_);
v_res_1505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1490_, v_post_1491_, v_usedLetOnly_boxed_1502_, v_skipConstInApp_boxed_1503_, v_skipInstances_boxed_1504_, v_e_1495_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_a_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1506_, lean_object* v_post_1507_, lean_object* v_usedLetOnly_1508_, lean_object* v_skipConstInApp_1509_, lean_object* v_skipInstances_1510_, lean_object* v_sz_1511_, lean_object* v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_usedLetOnly_boxed_1520_; uint8_t v_skipConstInApp_boxed_1521_; uint8_t v_skipInstances_boxed_1522_; size_t v_sz_boxed_1523_; size_t v_i_boxed_1524_; lean_object* v_res_1525_; 
v_usedLetOnly_boxed_1520_ = lean_unbox(v_usedLetOnly_1508_);
v_skipConstInApp_boxed_1521_ = lean_unbox(v_skipConstInApp_1509_);
v_skipInstances_boxed_1522_ = lean_unbox(v_skipInstances_1510_);
v_sz_boxed_1523_ = lean_unbox_usize(v_sz_1511_);
lean_dec(v_sz_1511_);
v_i_boxed_1524_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_res_1525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1506_, v_post_1507_, v_usedLetOnly_boxed_1520_, v_skipConstInApp_boxed_1521_, v_skipInstances_boxed_1522_, v_sz_boxed_1523_, v_i_boxed_1524_, v_bs_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1526_, lean_object* v_post_1527_, lean_object* v_usedLetOnly_1528_, lean_object* v_skipConstInApp_1529_, lean_object* v_skipInstances_1530_, lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_usedLetOnly_boxed_1538_; uint8_t v_skipConstInApp_boxed_1539_; uint8_t v_skipInstances_boxed_1540_; lean_object* v_res_1541_; 
v_usedLetOnly_boxed_1538_ = lean_unbox(v_usedLetOnly_1528_);
v_skipConstInApp_boxed_1539_ = lean_unbox(v_skipConstInApp_1529_);
v_skipInstances_boxed_1540_ = lean_unbox(v_skipInstances_1530_);
v_res_1541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1526_, v_post_1527_, v_usedLetOnly_boxed_1538_, v_skipConstInApp_boxed_1539_, v_skipInstances_boxed_1540_, v_e_1531_, v_a_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v_a_1532_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1542_, lean_object* v_post_1543_, lean_object* v_usedLetOnly_1544_, lean_object* v_skipConstInApp_1545_, lean_object* v_skipInstances_1546_, lean_object* v_fvars_1547_, lean_object* v_e_1548_, lean_object* v_a_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_usedLetOnly_boxed_1555_; uint8_t v_skipConstInApp_boxed_1556_; uint8_t v_skipInstances_boxed_1557_; lean_object* v_res_1558_; 
v_usedLetOnly_boxed_1555_ = lean_unbox(v_usedLetOnly_1544_);
v_skipConstInApp_boxed_1556_ = lean_unbox(v_skipConstInApp_1545_);
v_skipInstances_boxed_1557_ = lean_unbox(v_skipInstances_1546_);
v_res_1558_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1542_, v_post_1543_, v_usedLetOnly_boxed_1555_, v_skipConstInApp_boxed_1556_, v_skipInstances_boxed_1557_, v_fvars_1547_, v_e_1548_, v_a_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v_a_1549_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1559_, lean_object* v_post_1560_, lean_object* v_usedLetOnly_1561_, lean_object* v_skipConstInApp_1562_, lean_object* v_skipInstances_1563_, lean_object* v_fvars_1564_, lean_object* v_e_1565_, lean_object* v_a_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_usedLetOnly_boxed_1572_; uint8_t v_skipConstInApp_boxed_1573_; uint8_t v_skipInstances_boxed_1574_; lean_object* v_res_1575_; 
v_usedLetOnly_boxed_1572_ = lean_unbox(v_usedLetOnly_1561_);
v_skipConstInApp_boxed_1573_ = lean_unbox(v_skipConstInApp_1562_);
v_skipInstances_boxed_1574_ = lean_unbox(v_skipInstances_1563_);
v_res_1575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1559_, v_post_1560_, v_usedLetOnly_boxed_1572_, v_skipConstInApp_boxed_1573_, v_skipInstances_boxed_1574_, v_fvars_1564_, v_e_1565_, v_a_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v_a_1566_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1576_, lean_object* v_post_1577_, lean_object* v_usedLetOnly_1578_, lean_object* v_skipConstInApp_1579_, lean_object* v_skipInstances_1580_, lean_object* v_fvars_1581_, lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v_usedLetOnly_boxed_1589_; uint8_t v_skipConstInApp_boxed_1590_; uint8_t v_skipInstances_boxed_1591_; lean_object* v_res_1592_; 
v_usedLetOnly_boxed_1589_ = lean_unbox(v_usedLetOnly_1578_);
v_skipConstInApp_boxed_1590_ = lean_unbox(v_skipConstInApp_1579_);
v_skipInstances_boxed_1591_ = lean_unbox(v_skipInstances_1580_);
v_res_1592_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1576_, v_post_1577_, v_usedLetOnly_boxed_1589_, v_skipConstInApp_boxed_1590_, v_skipInstances_boxed_1591_, v_fvars_1581_, v_e_1582_, v_a_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v_a_1583_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1593_, lean_object* v___x_1594_, lean_object* v_pre_1595_, lean_object* v_post_1596_, lean_object* v_usedLetOnly_1597_, lean_object* v_skipConstInApp_1598_, lean_object* v_skipInstances_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v_usedLetOnly_boxed_1608_; uint8_t v_skipConstInApp_boxed_1609_; uint8_t v_skipInstances_boxed_1610_; lean_object* v_res_1611_; 
v_usedLetOnly_boxed_1608_ = lean_unbox(v_usedLetOnly_1597_);
v_skipConstInApp_boxed_1609_ = lean_unbox(v_skipConstInApp_1598_);
v_skipInstances_boxed_1610_ = lean_unbox(v_skipInstances_1599_);
v_res_1611_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1593_, v___x_1594_, v_pre_1595_, v_post_1596_, v_usedLetOnly_boxed_1608_, v_skipConstInApp_boxed_1609_, v_skipInstances_boxed_1610_, v_a_1600_, v_b_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___x_1594_);
lean_dec(v_upperBound_1593_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1612_, lean_object* v_pre_1613_, lean_object* v_post_1614_, lean_object* v_usedLetOnly_1615_, lean_object* v_skipConstInApp_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_skipInstances_boxed_1626_; uint8_t v_usedLetOnly_boxed_1627_; uint8_t v_skipConstInApp_boxed_1628_; lean_object* v_res_1629_; 
v_skipInstances_boxed_1626_ = lean_unbox(v_skipInstances_1612_);
v_usedLetOnly_boxed_1627_ = lean_unbox(v_usedLetOnly_1615_);
v_skipConstInApp_boxed_1628_ = lean_unbox(v_skipConstInApp_1616_);
v_res_1629_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1626_, v_pre_1613_, v_post_1614_, v_usedLetOnly_boxed_1627_, v_skipConstInApp_boxed_1628_, v_x_1617_, v_x_1618_, v_x_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_1630_; lean_object* v___x_1631_; 
v_cellCount_1630_ = lean_unsigned_to_nat(16u);
v___x_1631_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_1632_; lean_object* v___x_1633_; 
v_cellCount_1632_ = lean_unsigned_to_nat(16u);
v___x_1633_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1635_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1635_);
lean_ctor_set(v___x_1637_, 2, v___x_1634_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1639_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1639_, 0, lean_box(0));
lean_closure_set(v___x_1639_, 1, lean_box(0));
lean_closure_set(v___x_1639_, 2, v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1640_, lean_object* v_pre_1641_, lean_object* v_post_1642_, uint8_t v_usedLetOnly_1643_, uint8_t v_skipConstInApp_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_a_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1650_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3);
v___x_1651_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1650_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = 0;
v___x_1654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1641_, v_post_1642_, v_usedLetOnly_1643_, v_skipConstInApp_1644_, v___x_1653_, v_input_1640_, v_a_1652_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1656_, 0, lean_box(0));
lean_closure_set(v___x_1656_, 1, lean_box(0));
lean_closure_set(v___x_1656_, 2, v_a_1652_);
v___x_1657_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1656_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v___x_1657_, 0);
lean_dec(v_unused_1665_);
v___x_1659_ = v___x_1657_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v___x_1657_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v_a_1655_);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1655_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
lean_dec(v_a_1652_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1666_, lean_object* v_pre_1667_, lean_object* v_post_1668_, lean_object* v_usedLetOnly_1669_, lean_object* v_skipConstInApp_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_usedLetOnly_boxed_1676_; uint8_t v_skipConstInApp_boxed_1677_; lean_object* v_res_1678_; 
v_usedLetOnly_boxed_1676_ = lean_unbox(v_usedLetOnly_1669_);
v_skipConstInApp_boxed_1677_ = lean_unbox(v_skipConstInApp_1670_);
v_res_1678_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1666_, v_pre_1667_, v_post_1668_, v_usedLetOnly_boxed_1676_, v_skipConstInApp_boxed_1677_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1700_; 
v___x_1687_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1681_, v_a_1685_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1700_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1700_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_unbox(v_a_1688_);
lean_dec(v_a_1688_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1694_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v_e_1681_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_e_1681_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
lean_object* v___f_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_del_object(v___x_1690_);
v___f_1696_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1697_ = 0;
v___x_1698_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1699_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1681_, v___x_1698_, v___f_1696_, v___x_1697_, v___x_1697_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1708_, lean_object* v___x_1709_, lean_object* v_pre_1710_, lean_object* v_post_1711_, uint8_t v_usedLetOnly_1712_, uint8_t v_skipConstInApp_1713_, uint8_t v_skipInstances_1714_, lean_object* v___x_1715_, lean_object* v_inst_1716_, lean_object* v_R_1717_, lean_object* v_a_1718_, lean_object* v_b_1719_, lean_object* v_c_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1708_, v___x_1709_, v_pre_1710_, v_post_1711_, v_usedLetOnly_1712_, v_skipConstInApp_1713_, v_skipInstances_1714_, v_a_1718_, v_b_1719_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1728_ = _args[0];
lean_object* v___x_1729_ = _args[1];
lean_object* v_pre_1730_ = _args[2];
lean_object* v_post_1731_ = _args[3];
lean_object* v_usedLetOnly_1732_ = _args[4];
lean_object* v_skipConstInApp_1733_ = _args[5];
lean_object* v_skipInstances_1734_ = _args[6];
lean_object* v___x_1735_ = _args[7];
lean_object* v_inst_1736_ = _args[8];
lean_object* v_R_1737_ = _args[9];
lean_object* v_a_1738_ = _args[10];
lean_object* v_b_1739_ = _args[11];
lean_object* v_c_1740_ = _args[12];
lean_object* v___y_1741_ = _args[13];
lean_object* v___y_1742_ = _args[14];
lean_object* v___y_1743_ = _args[15];
lean_object* v___y_1744_ = _args[16];
lean_object* v___y_1745_ = _args[17];
lean_object* v___y_1746_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1747_; uint8_t v_skipConstInApp_boxed_1748_; uint8_t v_skipInstances_boxed_1749_; lean_object* v_res_1750_; 
v_usedLetOnly_boxed_1747_ = lean_unbox(v_usedLetOnly_1732_);
v_skipConstInApp_boxed_1748_ = lean_unbox(v_skipConstInApp_1733_);
v_skipInstances_boxed_1749_ = lean_unbox(v_skipInstances_1734_);
v_res_1750_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1728_, v___x_1729_, v_pre_1730_, v_post_1731_, v_usedLetOnly_boxed_1747_, v_skipConstInApp_boxed_1748_, v_skipInstances_boxed_1749_, v___x_1735_, v_inst_1736_, v_R_1737_, v_a_1738_, v_b_1739_, v_c_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec(v___x_1735_);
lean_dec_ref(v___x_1729_);
lean_dec(v_upperBound_1728_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1751_, lean_object* v_m_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1752_, v_a_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1755_, v_m_1756_, v_a_1757_);
lean_dec_ref(v_a_1757_);
lean_dec_ref(v_m_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1759_, lean_object* v_name_1760_, uint8_t v_bi_1761_, lean_object* v_type_1762_, lean_object* v_k_1763_, uint8_t v_kind_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1760_, v_bi_1761_, v_type_1762_, v_k_1763_, v_kind_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_name_1773_, lean_object* v_bi_1774_, lean_object* v_type_1775_, lean_object* v_k_1776_, lean_object* v_kind_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
uint8_t v_bi_boxed_1784_; uint8_t v_kind_boxed_1785_; lean_object* v_res_1786_; 
v_bi_boxed_1784_ = lean_unbox(v_bi_1774_);
v_kind_boxed_1785_ = lean_unbox(v_kind_1777_);
v_res_1786_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1772_, v_name_1773_, v_bi_boxed_1784_, v_type_1775_, v_k_1776_, v_kind_boxed_1785_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1787_, lean_object* v_name_1788_, lean_object* v_type_1789_, lean_object* v_val_1790_, lean_object* v_k_1791_, uint8_t v_nondep_1792_, uint8_t v_kind_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1788_, v_type_1789_, v_val_1790_, v_k_1791_, v_nondep_1792_, v_kind_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_name_1802_, lean_object* v_type_1803_, lean_object* v_val_1804_, lean_object* v_k_1805_, lean_object* v_nondep_1806_, lean_object* v_kind_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_nondep_boxed_1814_; uint8_t v_kind_boxed_1815_; lean_object* v_res_1816_; 
v_nondep_boxed_1814_ = lean_unbox(v_nondep_1806_);
v_kind_boxed_1815_ = lean_unbox(v_kind_1807_);
v_res_1816_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1801_, v_name_1802_, v_type_1803_, v_val_1804_, v_k_1805_, v_nondep_boxed_1814_, v_kind_boxed_1815_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1817_, lean_object* v_ref_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1818_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1825_, lean_object* v_ref_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1825_, v_ref_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1833_, lean_object* v_x_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1842_, lean_object* v_x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1842_, v_x_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1851_, lean_object* v_m_1852_, lean_object* v_query_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1852_, v_query_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___boxed(lean_object* v_00_u03b2_1855_, lean_object* v_m_1856_, lean_object* v_query_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(v_00_u03b2_1855_, v_m_1856_, v_query_1857_);
lean_dec_ref(v_query_1857_);
lean_dec_ref(v_m_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11(lean_object* v_00_u03b2_1859_, lean_object* v_m_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___redArg(v_m_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11___boxed(lean_object* v_00_u03b2_1862_, lean_object* v_m_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11(v_00_u03b2_1862_, v_m_1863_);
lean_dec_ref(v_m_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1865_, lean_object* v_m_1866_, lean_object* v_query_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_m_1866_, v_query_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1869_, lean_object* v_m_1870_, lean_object* v_query_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1869_, v_m_1870_, v_query_1871_);
lean_dec_ref(v_query_1871_);
lean_dec_ref(v_m_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1873_, lean_object* v_m_1874_, lean_object* v_query_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_m_1874_, v_query_1875_, v_x_1876_, v_x_1877_, v_x_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1881_, lean_object* v_m_1882_, lean_object* v_query_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1881_, v_m_1882_, v_query_1883_, v_x_1884_, v_x_1885_, v_x_1886_, v_x_1887_);
lean_dec_ref(v_query_1883_);
lean_dec_ref(v_m_1882_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17(lean_object* v_00_u03b2_1889_, lean_object* v_init_1890_, lean_object* v_b_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___redArg(v_init_1890_, v_b_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17___boxed(lean_object* v_00_u03b2_1893_, lean_object* v_init_1894_, lean_object* v_b_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17(v_00_u03b2_1893_, v_init_1894_, v_b_1895_);
lean_dec_ref(v_b_1895_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_1897_, lean_object* v_b_1898_, lean_object* v_acc_1899_, lean_object* v_i_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(v_b_1898_, v_acc_1899_, v_i_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18___boxed(lean_object* v_00_u03b2_1902_, lean_object* v_b_1903_, lean_object* v_acc_1904_, lean_object* v_i_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__11_spec__17_spec__18(v_00_u03b2_1902_, v_b_1903_, v_acc_1904_, v_i_1905_);
lean_dec_ref(v_b_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v_env_1914_; lean_object* v___x_1915_; lean_object* v_mctx_1916_; lean_object* v_lctx_1917_; lean_object* v_options_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1913_ = lean_st_ref_get(v___y_1911_);
v_env_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_env_1914_);
lean_dec(v___x_1913_);
v___x_1915_ = lean_st_ref_get(v___y_1909_);
v_mctx_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_mctx_1916_);
lean_dec(v___x_1915_);
v_lctx_1917_ = lean_ctor_get(v___y_1908_, 2);
v_options_1918_ = lean_ctor_get(v___y_1910_, 2);
lean_inc_ref(v_options_1918_);
lean_inc_ref(v_lctx_1917_);
v___x_1919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1919_, 0, v_env_1914_);
lean_ctor_set(v___x_1919_, 1, v_mctx_1916_);
lean_ctor_set(v___x_1919_, 2, v_lctx_1917_);
lean_ctor_set(v___x_1919_, 3, v_options_1918_);
v___x_1920_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v_msgData_1907_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1928_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1929_; double v___x_1930_; 
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = lean_float_of_nat(v___x_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1934_, lean_object* v_msg_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_ref_1941_; lean_object* v___x_1942_; lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1987_; 
v_ref_1941_ = lean_ctor_get(v___y_1938_, 5);
v___x_1942_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1987_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1987_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v_traceState_1948_; lean_object* v_env_1949_; lean_object* v_nextMacroScope_1950_; lean_object* v_ngen_1951_; lean_object* v_auxDeclNGen_1952_; lean_object* v_cache_1953_; lean_object* v_messages_1954_; lean_object* v_infoState_1955_; lean_object* v_snapshotTasks_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1986_; 
v___x_1947_ = lean_st_ref_take(v___y_1939_);
v_traceState_1948_ = lean_ctor_get(v___x_1947_, 4);
v_env_1949_ = lean_ctor_get(v___x_1947_, 0);
v_nextMacroScope_1950_ = lean_ctor_get(v___x_1947_, 1);
v_ngen_1951_ = lean_ctor_get(v___x_1947_, 2);
v_auxDeclNGen_1952_ = lean_ctor_get(v___x_1947_, 3);
v_cache_1953_ = lean_ctor_get(v___x_1947_, 5);
v_messages_1954_ = lean_ctor_get(v___x_1947_, 6);
v_infoState_1955_ = lean_ctor_get(v___x_1947_, 7);
v_snapshotTasks_1956_ = lean_ctor_get(v___x_1947_, 8);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1958_ = v___x_1947_;
v_isShared_1959_ = v_isSharedCheck_1986_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_snapshotTasks_1956_);
lean_inc(v_infoState_1955_);
lean_inc(v_messages_1954_);
lean_inc(v_cache_1953_);
lean_inc(v_traceState_1948_);
lean_inc(v_auxDeclNGen_1952_);
lean_inc(v_ngen_1951_);
lean_inc(v_nextMacroScope_1950_);
lean_inc(v_env_1949_);
lean_dec(v___x_1947_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1986_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
uint64_t v_tid_1960_; lean_object* v_traces_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1985_; 
v_tid_1960_ = lean_ctor_get_uint64(v_traceState_1948_, sizeof(void*)*1);
v_traces_1961_ = lean_ctor_get(v_traceState_1948_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_traceState_1948_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1963_ = v_traceState_1948_;
v_isShared_1964_ = v_isSharedCheck_1985_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_traces_1961_);
lean_dec(v_traceState_1948_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1985_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; double v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1967_ = 0;
v___x_1968_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1969_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1969_, 0, v_cls_1934_);
lean_ctor_set(v___x_1969_, 1, v___x_1965_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
lean_ctor_set_float(v___x_1969_, sizeof(void*)*3, v___x_1966_);
lean_ctor_set_float(v___x_1969_, sizeof(void*)*3 + 8, v___x_1966_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*3 + 16, v___x_1967_);
v___x_1970_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1971_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v_a_1943_);
lean_ctor_set(v___x_1971_, 2, v___x_1970_);
lean_inc(v_ref_1941_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_ref_1941_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = l_Lean_PersistentArray_push___redArg(v_traces_1961_, v___x_1972_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1973_);
v___x_1975_ = v___x_1963_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1973_);
lean_ctor_set_uint64(v_reuseFailAlloc_1984_, sizeof(void*)*1, v_tid_1960_);
v___x_1975_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v___x_1975_);
v___x_1977_ = v___x_1958_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_env_1949_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_nextMacroScope_1950_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_ngen_1951_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_auxDeclNGen_1952_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 5, v_cache_1953_);
lean_ctor_set(v_reuseFailAlloc_1983_, 6, v_messages_1954_);
lean_ctor_set(v_reuseFailAlloc_1983_, 7, v_infoState_1955_);
lean_ctor_set(v_reuseFailAlloc_1983_, 8, v_snapshotTasks_1956_);
v___x_1977_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1978_ = lean_st_ref_put(v___y_1939_, v___x_1977_);
v___x_1979_ = lean_box(0);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1979_);
v___x_1981_ = v___x_1945_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1988_, lean_object* v_msg_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1988_, v_msg_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
return v_res_1995_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2000_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__1));
v___x_2001_ = l_Lean_Name_append(v___x_2000_, v___x_1999_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__3));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__5));
v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__7));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__9));
v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_e_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
if (lean_obj_tag(v_e_2014_) == 11)
{
lean_object* v_typeName_2026_; lean_object* v_idx_2027_; lean_object* v_struct_2028_; lean_object* v___x_2029_; lean_object* v_env_2030_; lean_object* v___x_2031_; 
v_typeName_2026_ = lean_ctor_get(v_e_2014_, 0);
v_idx_2027_ = lean_ctor_get(v_e_2014_, 1);
v_struct_2028_ = lean_ctor_get(v_e_2014_, 2);
v___x_2029_ = lean_st_ref_get(v___y_2018_);
v_env_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_ref(v_env_2030_);
lean_dec(v___x_2029_);
lean_inc(v_typeName_2026_);
v___x_2031_ = l_Lean_getStructureInfo_x3f(v_env_2030_, v_typeName_2026_);
if (lean_obj_tag(v___x_2031_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2100_; 
v_val_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2100_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2100_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_fieldNames_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v_fieldNames_2036_ = lean_ctor_get(v_val_2032_, 1);
lean_inc_ref(v_fieldNames_2036_);
lean_dec(v_val_2032_);
v___x_2037_ = lean_array_get_size(v_fieldNames_2036_);
v___x_2038_ = lean_nat_dec_lt(v_idx_2027_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v_options_2039_; uint8_t v_hasTrace_2040_; 
lean_dec_ref(v_fieldNames_2036_);
v_options_2039_ = lean_ctor_get(v___y_2017_, 2);
v_hasTrace_2040_ = lean_ctor_get_uint8(v_options_2039_, sizeof(void*)*1);
if (v_hasTrace_2040_ == 0)
{
lean_del_object(v___x_2034_);
goto v___jp_2020_;
}
else
{
lean_object* v_inheritedTraceOptions_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_inheritedTraceOptions_2041_ = lean_ctor_get(v___y_2017_, 13);
v___x_2042_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2043_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_2044_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2041_, v_options_2039_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_del_object(v___x_2034_);
goto v___jp_2020_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4);
lean_inc(v_idx_2027_);
v___x_2046_ = l_Nat_reprFast(v_idx_2027_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 3);
lean_ctor_set(v___x_2034_, 0, v___x_2046_);
v___x_2048_ = v___x_2034_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2049_ = l_Lean_MessageData_ofFormat(v___x_2048_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2045_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
lean_inc_ref(v_e_2014_);
v___x_2053_ = l_Lean_indentExpr(v_e_2014_);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2042_, v___x_2054_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
goto v___jp_2020_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref_known(v_e_2014_, 3);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
}
else
{
lean_object* v_keyedConfig_2065_; uint8_t v_trackZetaDelta_2066_; lean_object* v_zetaDeltaSet_2067_; lean_object* v_lctx_2068_; lean_object* v_localInstances_2069_; lean_object* v_defEqCtx_x3f_2070_; lean_object* v_synthPendingDepth_2071_; lean_object* v_customCanUnfoldPredicate_x3f_2072_; uint8_t v_univApprox_2073_; uint8_t v_inTypeClassResolution_2074_; uint8_t v_cacheInferType_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_inc_ref(v_struct_2028_);
lean_inc(v_idx_2027_);
lean_dec_ref_known(v_e_2014_, 3);
v_keyedConfig_2065_ = lean_ctor_get(v___y_2015_, 0);
v_trackZetaDelta_2066_ = lean_ctor_get_uint8(v___y_2015_, sizeof(void*)*7);
v_zetaDeltaSet_2067_ = lean_ctor_get(v___y_2015_, 1);
v_lctx_2068_ = lean_ctor_get(v___y_2015_, 2);
v_localInstances_2069_ = lean_ctor_get(v___y_2015_, 3);
v_defEqCtx_x3f_2070_ = lean_ctor_get(v___y_2015_, 4);
v_synthPendingDepth_2071_ = lean_ctor_get(v___y_2015_, 5);
v_customCanUnfoldPredicate_x3f_2072_ = lean_ctor_get(v___y_2015_, 6);
v_univApprox_2073_ = lean_ctor_get_uint8(v___y_2015_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2074_ = lean_ctor_get_uint8(v___y_2015_, sizeof(void*)*7 + 2);
v_cacheInferType_2075_ = lean_ctor_get_uint8(v___y_2015_, sizeof(void*)*7 + 3);
v___x_2076_ = lean_array_fget(v_fieldNames_2036_, v_idx_2027_);
lean_dec(v_idx_2027_);
lean_dec_ref(v_fieldNames_2036_);
v___x_2077_ = 1;
lean_inc_ref(v_keyedConfig_2065_);
v___x_2078_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2077_, v_keyedConfig_2065_);
lean_inc(v_customCanUnfoldPredicate_x3f_2072_);
lean_inc(v_synthPendingDepth_2071_);
lean_inc(v_defEqCtx_x3f_2070_);
lean_inc_ref(v_localInstances_2069_);
lean_inc_ref(v_lctx_2068_);
lean_inc(v_zetaDeltaSet_2067_);
v___x_2079_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_zetaDeltaSet_2067_);
lean_ctor_set(v___x_2079_, 2, v_lctx_2068_);
lean_ctor_set(v___x_2079_, 3, v_localInstances_2069_);
lean_ctor_set(v___x_2079_, 4, v_defEqCtx_x3f_2070_);
lean_ctor_set(v___x_2079_, 5, v_synthPendingDepth_2071_);
lean_ctor_set(v___x_2079_, 6, v_customCanUnfoldPredicate_x3f_2072_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*7, v_trackZetaDelta_2066_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*7 + 1, v_univApprox_2073_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2074_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*7 + 3, v_cacheInferType_2075_);
v___x_2080_ = l_Lean_Meta_mkProjection(v_struct_2028_, v___x_2076_, v___x_2079_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec_ref_known(v___x_2079_, 7);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2091_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_a_2081_);
v___x_2086_ = v___x_2034_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2086_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_del_object(v___x_2034_);
v_a_2092_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2080_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2080_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
else
{
lean_object* v_options_2101_; uint8_t v_hasTrace_2102_; 
lean_dec(v___x_2031_);
v_options_2101_ = lean_ctor_get(v___y_2017_, 2);
v_hasTrace_2102_ = lean_ctor_get_uint8(v_options_2101_, sizeof(void*)*1);
if (v_hasTrace_2102_ == 0)
{
goto v___jp_2023_;
}
else
{
lean_object* v_inheritedTraceOptions_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_inheritedTraceOptions_2103_ = lean_ctor_get(v___y_2017_, 13);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2105_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_2106_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2103_, v_options_2101_, v___x_2105_);
if (v___x_2106_ == 0)
{
goto v___jp_2023_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2107_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__8);
lean_inc(v_typeName_2026_);
v___x_2108_ = l_Lean_MessageData_ofName(v_typeName_2026_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_inc_ref(v_e_2014_);
v___x_2112_ = l_Lean_indentExpr(v_e_2014_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2104_, v___x_2113_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_dec_ref_known(v___x_2114_, 1);
goto v___jp_2023_;
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref_known(v_e_2014_, 3);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_e_2014_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_e_2014_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
v___jp_2023_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_e_2014_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_e_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_e_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_x_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_x_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_x_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec_ref(v_x_2140_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; 
v___f_2156_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2157_ = lean_find_expr(v___f_2156_, v_e_2150_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_e_2150_);
return v___x_2158_;
}
else
{
lean_object* v_post_2159_; lean_object* v___f_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref_known(v___x_2157_, 1);
v_post_2159_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v___f_2160_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2161_ = 0;
v___x_2162_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2150_, v___f_2160_, v_post_2159_, v___x_2161_, v___x_2161_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Meta_Sym_foldProjs(v_e_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2175_ = l_Lean_mkConst(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2181_ = l_Lean_mkConst(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_box(0);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2189_ = l_Lean_mkConst(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_box(0);
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2196_ = l_Lean_mkConst(v___x_2195_, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = l_Lean_mkNatLit(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2206_ = l_Lean_mkConst(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2210_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2209_, v_a_2207_, v_a_2208_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v_a_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
v_a_2212_ = lean_ctor_get(v___x_2210_, 1);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2210_, 2);
v___x_2213_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2214_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2213_, v_a_2207_, v_a_2212_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
v_a_2216_ = lean_ctor_get(v___x_2214_, 1);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2214_, 2);
v___x_2217_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2218_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2217_, v_a_2207_, v_a_2216_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
v_a_2220_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2218_, 2);
v___x_2221_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2221_, v_a_2207_, v_a_2220_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v_a_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
v_a_2224_ = lean_ctor_get(v___x_2222_, 1);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2222_, 2);
v___x_2225_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2226_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2225_, v_a_2207_, v_a_2224_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
v_a_2228_ = lean_ctor_get(v___x_2226_, 1);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2226_, 2);
v___x_2229_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2230_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2229_, v_a_2207_, v_a_2228_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
v_a_2232_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2230_, 2);
v___x_2233_ = l_Lean_Int_mkType;
v___x_2234_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2233_, v_a_2207_, v_a_2232_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_a_2236_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2215_);
lean_ctor_set(v___x_2240_, 1, v_a_2211_);
lean_ctor_set(v___x_2240_, 2, v_a_2227_);
lean_ctor_set(v___x_2240_, 3, v_a_2223_);
lean_ctor_set(v___x_2240_, 4, v_a_2219_);
lean_ctor_set(v___x_2240_, 5, v_a_2231_);
lean_ctor_set(v___x_2240_, 6, v_a_2235_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_a_2236_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_a_2231_);
lean_dec(v_a_2227_);
lean_dec(v_a_2223_);
lean_dec(v_a_2219_);
lean_dec(v_a_2215_);
lean_dec(v_a_2211_);
v_a_2245_ = lean_ctor_get(v___x_2234_, 0);
v_a_2246_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2234_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_inc(v_a_2245_);
lean_dec(v___x_2234_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2245_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2227_);
lean_dec(v_a_2223_);
lean_dec(v_a_2219_);
lean_dec(v_a_2215_);
lean_dec(v_a_2211_);
v_a_2254_ = lean_ctor_get(v___x_2230_, 0);
v_a_2255_ = lean_ctor_get(v___x_2230_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2230_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_inc(v_a_2254_);
lean_dec(v___x_2230_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2254_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2223_);
lean_dec(v_a_2219_);
lean_dec(v_a_2215_);
lean_dec(v_a_2211_);
v_a_2263_ = lean_ctor_get(v___x_2226_, 0);
v_a_2264_ = lean_ctor_get(v___x_2226_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2226_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_inc(v_a_2263_);
lean_dec(v___x_2226_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2263_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_a_2219_);
lean_dec(v_a_2215_);
lean_dec(v_a_2211_);
v_a_2272_ = lean_ctor_get(v___x_2222_, 0);
v_a_2273_ = lean_ctor_get(v___x_2222_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2222_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_inc(v_a_2272_);
lean_dec(v___x_2222_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2272_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2215_);
lean_dec(v_a_2211_);
v_a_2281_ = lean_ctor_get(v___x_2218_, 0);
v_a_2282_ = lean_ctor_get(v___x_2218_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2218_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_inc(v_a_2281_);
lean_dec(v___x_2218_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2281_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2211_);
v_a_2290_ = lean_ctor_get(v___x_2214_, 0);
v_a_2291_ = lean_ctor_get(v___x_2214_, 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2214_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_inc(v_a_2290_);
lean_dec(v___x_2214_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2290_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v_a_2299_ = lean_ctor_get(v___x_2210_, 0);
v_a_2300_ = lean_ctor_get(v___x_2210_, 1);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2210_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_inc(v_a_2299_);
lean_dec(v___x_2210_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2299_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2308_, v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2311_, lean_object* v_opt_2312_){
_start:
{
lean_object* v_name_2313_; lean_object* v_defValue_2314_; lean_object* v_map_2315_; lean_object* v___x_2316_; 
v_name_2313_ = lean_ctor_get(v_opt_2312_, 0);
v_defValue_2314_ = lean_ctor_get(v_opt_2312_, 1);
v_map_2315_ = lean_ctor_get(v_opts_2311_, 0);
v___x_2316_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2315_, v_name_2313_);
if (lean_obj_tag(v___x_2316_) == 0)
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_unbox(v_defValue_2314_);
return v___x_2317_;
}
else
{
lean_object* v_val_2318_; 
v_val_2318_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v___x_2316_, 1);
if (lean_obj_tag(v_val_2318_) == 1)
{
uint8_t v_v_2319_; 
v_v_2319_ = lean_ctor_get_uint8(v_val_2318_, 0);
lean_dec_ref_known(v_val_2318_, 0);
return v_v_2319_;
}
else
{
uint8_t v___x_2320_; 
lean_dec(v_val_2318_);
v___x_2320_ = lean_unbox(v_defValue_2314_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2321_, lean_object* v_opt_2322_){
_start:
{
uint8_t v_res_2323_; lean_object* v_r_2324_; 
v_res_2323_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2321_, v_opt_2322_);
lean_dec_ref(v_opt_2322_);
lean_dec_ref(v_opts_2321_);
v_r_2324_ = lean_box(v_res_2323_);
return v_r_2324_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___f_2337_; lean_object* v___x_2112__overap_2338_; lean_object* v___x_2339_; 
v___f_2337_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2112__overap_2338_ = lean_panic_fn_borrowed(v___f_2337_, v_msg_2331_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
v___x_2339_ = lean_apply_5(v___x_2112__overap_2338_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, lean_box(0));
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2346_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
return v___x_2351_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_box(0));
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_2357_ = lean_unsigned_to_nat(19u);
v___x_2358_ = lean_unsigned_to_nat(304u);
v___x_2359_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__5));
v___x_2360_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2361_ = l_mkPanicMessageWithDecl(v___x_2360_, v___x_2359_, v___x_2358_, v___x_2357_, v___x_2356_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_fst_2369_; lean_object* v_snd_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___x_2410_; lean_object* v_env_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2410_ = lean_st_ref_get(v_a_2366_);
v_env_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc_ref(v_env_2411_);
lean_dec(v___x_2410_);
v___x_2412_ = 0;
v___x_2413_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2413_, 0, v_env_2411_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1, v___x_2412_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1 + 1, v___x_2412_);
v___x_2414_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
v___x_2415_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2413_, v___x_2414_);
lean_dec_ref_known(v___x_2413_, 1);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v_a_2417_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
v_a_2417_ = lean_ctor_get(v___x_2415_, 1);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2415_, 2);
v_fst_2369_ = v_a_2416_;
v_snd_2370_ = v_a_2417_;
v___y_2371_ = v_a_2363_;
v___y_2372_ = v_a_2364_;
v___y_2373_ = v_a_2365_;
v___y_2374_ = v_a_2366_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref_known(v___x_2415_, 2);
v___x_2418_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__7, &l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7);
v___x_2419_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2418_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v_fst_2421_; lean_object* v_snd_2422_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v_fst_2421_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_fst_2421_);
v_snd_2422_ = lean_ctor_get(v_a_2420_, 1);
lean_inc(v_snd_2422_);
lean_dec(v_a_2420_);
v_fst_2369_ = v_fst_2421_;
v_snd_2370_ = v_snd_2422_;
v___y_2371_ = v_a_2363_;
v___y_2372_ = v_a_2364_;
v___y_2373_ = v_a_2365_;
v___y_2374_ = v_a_2366_;
goto v___jp_2368_;
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec_ref(v_x_2362_);
v_a_2423_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2419_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2419_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
v___jp_2368_:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v_options_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v_options_2377_ = lean_ctor_get(v___y_2373_, 2);
v___x_2378_ = l_Lean_Meta_Sym_sym_debug;
v___x_2379_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_options_2377_, v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2381_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_2384_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v___x_2384_, 0, v_snd_2370_);
lean_ctor_set(v___x_2384_, 1, v___x_2381_);
lean_ctor_set(v___x_2384_, 2, v___x_2381_);
lean_ctor_set(v___x_2384_, 3, v___x_2381_);
lean_ctor_set(v___x_2384_, 4, v___x_2381_);
lean_ctor_set(v___x_2384_, 5, v___x_2381_);
lean_ctor_set(v___x_2384_, 6, v___x_2381_);
lean_ctor_set(v___x_2384_, 7, v_a_2376_);
lean_ctor_set(v___x_2384_, 8, v___x_2382_);
lean_ctor_set(v___x_2384_, 9, v___x_2383_);
lean_ctor_set(v___x_2384_, 10, v___x_2381_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*11, v___x_2379_);
v___x_2385_ = lean_st_mk_ref(v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_fst_2369_);
lean_ctor_set(v___x_2386_, 1, v___x_2380_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
lean_inc(v___x_2385_);
v___x_2387_ = lean_apply_7(v_x_2362_, v___x_2386_, v___x_2385_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, lean_box(0));
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2396_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_st_ref_get(v___x_2385_);
lean_dec(v___x_2385_);
lean_dec(v___x_2392_);
if (v_isShared_2391_ == 0)
{
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2388_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_dec(v___x_2385_);
return v___x_2387_;
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v_snd_2370_);
lean_dec_ref(v_fst_2369_);
lean_dec_ref(v_x_2362_);
v_a_2397_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2399_ = v___x_2375_;
v_isShared_2400_ = v_isSharedCheck_2409_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2375_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2409_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_ref_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v_ref_2401_ = lean_ctor_get(v___y_2373_, 5);
v___x_2402_ = lean_io_error_to_string(v_a_2397_);
v___x_2403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
v___x_2404_ = l_Lean_MessageData_ofFormat(v___x_2403_);
lean_inc(v_ref_2401_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_ref_2401_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2405_);
v___x_2407_ = v___x_2399_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2438_, lean_object* v_x_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2446_, lean_object* v_x_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2446_, v_x_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2454_){
_start:
{
lean_object* v_sharedExprs_2456_; lean_object* v___x_2457_; 
v_sharedExprs_2456_ = lean_ctor_get(v_a_2454_, 0);
lean_inc_ref(v_sharedExprs_2456_);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_sharedExprs_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2458_);
lean_dec_ref(v_a_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2461_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2488_; 
v___x_2479_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2477_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_trueExpr_2484_; lean_object* v___x_2486_; 
v_trueExpr_2484_ = lean_ctor_get(v_a_2480_, 0);
lean_inc_ref(v_trueExpr_2484_);
lean_dec(v_a_2480_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v_trueExpr_2484_);
v___x_2486_ = v___x_2482_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_trueExpr_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2489_);
lean_dec_ref(v_a_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2492_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2509_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2523_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2523_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2523_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
size_t v___x_2516_; size_t v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2516_ = lean_ptr_addr(v_e_2508_);
v___x_2517_ = lean_ptr_addr(v_a_2512_);
lean_dec(v_a_2512_);
v___x_2518_ = lean_usize_dec_eq(v___x_2516_, v___x_2517_);
v___x_2519_ = lean_box(v___x_2518_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2519_);
v___x_2521_ = v___x_2514_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2511_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2511_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2532_, v_a_2533_);
lean_dec_ref(v_a_2533_);
lean_dec_ref(v_e_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2536_, v_a_2537_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec_ref(v_e_2545_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
v___x_2556_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2554_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_falseExpr_2561_; lean_object* v___x_2563_; 
v_falseExpr_2561_ = lean_ctor_get(v_a_2557_, 1);
lean_inc_ref(v_falseExpr_2561_);
lean_dec(v_a_2557_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_falseExpr_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_falseExpr_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2566_);
lean_dec_ref(v_a_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2569_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2586_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2600_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2600_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2600_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
size_t v___x_2593_; size_t v___x_2594_; uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2593_ = lean_ptr_addr(v_e_2585_);
v___x_2594_ = lean_ptr_addr(v_a_2589_);
lean_dec(v_a_2589_);
v___x_2595_ = lean_usize_dec_eq(v___x_2593_, v___x_2594_);
v___x_2596_ = lean_box(v___x_2595_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2596_);
v___x_2598_ = v___x_2591_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
v_a_2601_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2588_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2588_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2609_, v_a_2610_);
lean_dec_ref(v_a_2610_);
lean_dec_ref(v_e_2609_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2613_, v_a_2614_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec_ref(v_e_2622_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v___x_2633_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2631_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_btrueExpr_2638_; lean_object* v___x_2640_; 
v_btrueExpr_2638_ = lean_ctor_get(v_a_2634_, 3);
lean_inc_ref(v_btrueExpr_2638_);
lean_dec(v_a_2634_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v_btrueExpr_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_btrueExpr_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2643_);
lean_dec_ref(v_a_2643_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2646_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2677_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2677_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2677_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
size_t v___x_2670_; size_t v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2670_ = lean_ptr_addr(v_e_2662_);
v___x_2671_ = lean_ptr_addr(v_a_2666_);
lean_dec(v_a_2666_);
v___x_2672_ = lean_usize_dec_eq(v___x_2670_, v___x_2671_);
v___x_2673_ = lean_box(v___x_2672_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2665_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2665_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2686_, v_a_2687_);
lean_dec_ref(v_a_2687_);
lean_dec_ref(v_e_2686_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2690_, v_a_2691_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec_ref(v_e_2699_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2710_; lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2719_; 
v___x_2710_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2708_);
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_bfalseExpr_2715_; lean_object* v___x_2717_; 
v_bfalseExpr_2715_ = lean_ctor_get(v_a_2711_, 4);
lean_inc_ref(v_bfalseExpr_2715_);
lean_dec(v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_bfalseExpr_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_bfalseExpr_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2720_);
lean_dec_ref(v_a_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2723_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2740_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2754_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2754_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2754_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
size_t v___x_2747_; size_t v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2747_ = lean_ptr_addr(v_e_2739_);
v___x_2748_ = lean_ptr_addr(v_a_2743_);
lean_dec(v_a_2743_);
v___x_2749_ = lean_usize_dec_eq(v___x_2747_, v___x_2748_);
v___x_2750_ = lean_box(v___x_2749_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2750_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2742_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2742_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2763_, v_a_2764_);
lean_dec_ref(v_a_2764_);
lean_dec_ref(v_e_2763_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2767_, v_a_2768_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec_ref(v_e_2776_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2796_; 
v___x_2787_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2785_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2796_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2796_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_natZExpr_2792_; lean_object* v___x_2794_; 
v_natZExpr_2792_ = lean_ctor_get(v_a_2788_, 2);
lean_inc_ref(v_natZExpr_2792_);
lean_dec(v_a_2788_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_natZExpr_2792_);
v___x_2794_ = v___x_2790_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_natZExpr_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2797_);
lean_dec_ref(v_a_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2800_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2816_){
_start:
{
lean_object* v___x_2818_; lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2827_; 
v___x_2818_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2816_);
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_ordEqExpr_2823_; lean_object* v___x_2825_; 
v_ordEqExpr_2823_ = lean_ctor_get(v_a_2819_, 5);
lean_inc_ref(v_ordEqExpr_2823_);
lean_dec(v_a_2819_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_ordEqExpr_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_ordEqExpr_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2828_);
lean_dec_ref(v_a_2828_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2831_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2858_; 
v___x_2849_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2847_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_intExpr_2854_; lean_object* v___x_2856_; 
v_intExpr_2854_ = lean_ctor_get(v_a_2850_, 6);
lean_inc_ref(v_intExpr_2854_);
lean_dec(v_a_2850_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v_intExpr_2854_);
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_intExpr_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2859_);
lean_dec_ref(v_a_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2862_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Meta_Sym_getIntExpr(v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2878_, lean_object* v_ctx_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v_share_2883_; lean_object* v_maxFVar_2884_; lean_object* v_proofInstInfo_2885_; lean_object* v_inferType_2886_; lean_object* v_getLevel_2887_; lean_object* v_congrInfo_2888_; lean_object* v_defEqI_2889_; lean_object* v_extensions_2890_; lean_object* v_issues_2891_; lean_object* v_canon_2892_; lean_object* v_instanceOverrides_2893_; uint8_t v_debug_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2954_; 
v___x_2882_ = lean_st_ref_take(v_a_2880_);
v_share_2883_ = lean_ctor_get(v___x_2882_, 0);
v_maxFVar_2884_ = lean_ctor_get(v___x_2882_, 1);
v_proofInstInfo_2885_ = lean_ctor_get(v___x_2882_, 2);
v_inferType_2886_ = lean_ctor_get(v___x_2882_, 3);
v_getLevel_2887_ = lean_ctor_get(v___x_2882_, 4);
v_congrInfo_2888_ = lean_ctor_get(v___x_2882_, 5);
v_defEqI_2889_ = lean_ctor_get(v___x_2882_, 6);
v_extensions_2890_ = lean_ctor_get(v___x_2882_, 7);
v_issues_2891_ = lean_ctor_get(v___x_2882_, 8);
v_canon_2892_ = lean_ctor_get(v___x_2882_, 9);
v_instanceOverrides_2893_ = lean_ctor_get(v___x_2882_, 10);
v_debug_2894_ = lean_ctor_get_uint8(v___x_2882_, sizeof(void*)*11);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2896_ = v___x_2882_;
v_isShared_2897_ = v_isSharedCheck_2954_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_instanceOverrides_2893_);
lean_inc(v_canon_2892_);
lean_inc(v_issues_2891_);
lean_inc(v_extensions_2890_);
lean_inc(v_defEqI_2889_);
lean_inc(v_congrInfo_2888_);
lean_inc(v_getLevel_2887_);
lean_inc(v_inferType_2886_);
lean_inc(v_proofInstInfo_2885_);
lean_inc(v_maxFVar_2884_);
lean_inc(v_share_2883_);
lean_dec(v___x_2882_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2954_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_maxFVar_2884_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_proofInstInfo_2885_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_inferType_2886_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_getLevel_2887_);
lean_ctor_set(v_reuseFailAlloc_2953_, 5, v_congrInfo_2888_);
lean_ctor_set(v_reuseFailAlloc_2953_, 6, v_defEqI_2889_);
lean_ctor_set(v_reuseFailAlloc_2953_, 7, v_extensions_2890_);
lean_ctor_set(v_reuseFailAlloc_2953_, 8, v_issues_2891_);
lean_ctor_set(v_reuseFailAlloc_2953_, 9, v_canon_2892_);
lean_ctor_set(v_reuseFailAlloc_2953_, 10, v_instanceOverrides_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2953_, sizeof(void*)*11, v_debug_2894_);
v___x_2900_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_st_ref_put(v_a_2880_, v___x_2900_);
v___x_2902_ = lean_apply_2(v_k_2878_, v_ctx_2879_, v_share_2883_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v_maxFVar_2906_; lean_object* v_proofInstInfo_2907_; lean_object* v_inferType_2908_; lean_object* v_getLevel_2909_; lean_object* v_congrInfo_2910_; lean_object* v_defEqI_2911_; lean_object* v_extensions_2912_; lean_object* v_issues_2913_; lean_object* v_canon_2914_; lean_object* v_instanceOverrides_2915_; uint8_t v_debug_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2926_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
v_a_2904_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2902_, 2);
v___x_2905_ = lean_st_ref_take(v_a_2880_);
v_maxFVar_2906_ = lean_ctor_get(v___x_2905_, 1);
v_proofInstInfo_2907_ = lean_ctor_get(v___x_2905_, 2);
v_inferType_2908_ = lean_ctor_get(v___x_2905_, 3);
v_getLevel_2909_ = lean_ctor_get(v___x_2905_, 4);
v_congrInfo_2910_ = lean_ctor_get(v___x_2905_, 5);
v_defEqI_2911_ = lean_ctor_get(v___x_2905_, 6);
v_extensions_2912_ = lean_ctor_get(v___x_2905_, 7);
v_issues_2913_ = lean_ctor_get(v___x_2905_, 8);
v_canon_2914_ = lean_ctor_get(v___x_2905_, 9);
v_instanceOverrides_2915_ = lean_ctor_get(v___x_2905_, 10);
v_debug_2916_ = lean_ctor_get_uint8(v___x_2905_, sizeof(void*)*11);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v___x_2905_, 0);
lean_dec(v_unused_2927_);
v___x_2918_ = v___x_2905_;
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_instanceOverrides_2915_);
lean_inc(v_canon_2914_);
lean_inc(v_issues_2913_);
lean_inc(v_extensions_2912_);
lean_inc(v_defEqI_2911_);
lean_inc(v_congrInfo_2910_);
lean_inc(v_getLevel_2909_);
lean_inc(v_inferType_2908_);
lean_inc(v_proofInstInfo_2907_);
lean_inc(v_maxFVar_2906_);
lean_dec(v___x_2905_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v_a_2904_);
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2904_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_maxFVar_2906_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_proofInstInfo_2907_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_inferType_2908_);
lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_getLevel_2909_);
lean_ctor_set(v_reuseFailAlloc_2925_, 5, v_congrInfo_2910_);
lean_ctor_set(v_reuseFailAlloc_2925_, 6, v_defEqI_2911_);
lean_ctor_set(v_reuseFailAlloc_2925_, 7, v_extensions_2912_);
lean_ctor_set(v_reuseFailAlloc_2925_, 8, v_issues_2913_);
lean_ctor_set(v_reuseFailAlloc_2925_, 9, v_canon_2914_);
lean_ctor_set(v_reuseFailAlloc_2925_, 10, v_instanceOverrides_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2925_, sizeof(void*)*11, v_debug_2916_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = lean_st_ref_put(v_a_2880_, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_a_2903_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v_a_2929_; lean_object* v___x_2930_; lean_object* v_maxFVar_2931_; lean_object* v_proofInstInfo_2932_; lean_object* v_inferType_2933_; lean_object* v_getLevel_2934_; lean_object* v_congrInfo_2935_; lean_object* v_defEqI_2936_; lean_object* v_extensions_2937_; lean_object* v_issues_2938_; lean_object* v_canon_2939_; lean_object* v_instanceOverrides_2940_; uint8_t v_debug_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2951_; 
v_a_2928_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2928_);
v_a_2929_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2902_, 2);
v___x_2930_ = lean_st_ref_take(v_a_2880_);
v_maxFVar_2931_ = lean_ctor_get(v___x_2930_, 1);
v_proofInstInfo_2932_ = lean_ctor_get(v___x_2930_, 2);
v_inferType_2933_ = lean_ctor_get(v___x_2930_, 3);
v_getLevel_2934_ = lean_ctor_get(v___x_2930_, 4);
v_congrInfo_2935_ = lean_ctor_get(v___x_2930_, 5);
v_defEqI_2936_ = lean_ctor_get(v___x_2930_, 6);
v_extensions_2937_ = lean_ctor_get(v___x_2930_, 7);
v_issues_2938_ = lean_ctor_get(v___x_2930_, 8);
v_canon_2939_ = lean_ctor_get(v___x_2930_, 9);
v_instanceOverrides_2940_ = lean_ctor_get(v___x_2930_, 10);
v_debug_2941_ = lean_ctor_get_uint8(v___x_2930_, sizeof(void*)*11);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v___x_2930_, 0);
lean_dec(v_unused_2952_);
v___x_2943_ = v___x_2930_;
v_isShared_2944_ = v_isSharedCheck_2951_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_instanceOverrides_2940_);
lean_inc(v_canon_2939_);
lean_inc(v_issues_2938_);
lean_inc(v_extensions_2937_);
lean_inc(v_defEqI_2936_);
lean_inc(v_congrInfo_2935_);
lean_inc(v_getLevel_2934_);
lean_inc(v_inferType_2933_);
lean_inc(v_proofInstInfo_2932_);
lean_inc(v_maxFVar_2931_);
lean_dec(v___x_2930_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2951_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v_a_2929_);
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2929_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_maxFVar_2931_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v_proofInstInfo_2932_);
lean_ctor_set(v_reuseFailAlloc_2950_, 3, v_inferType_2933_);
lean_ctor_set(v_reuseFailAlloc_2950_, 4, v_getLevel_2934_);
lean_ctor_set(v_reuseFailAlloc_2950_, 5, v_congrInfo_2935_);
lean_ctor_set(v_reuseFailAlloc_2950_, 6, v_defEqI_2936_);
lean_ctor_set(v_reuseFailAlloc_2950_, 7, v_extensions_2937_);
lean_ctor_set(v_reuseFailAlloc_2950_, 8, v_issues_2938_);
lean_ctor_set(v_reuseFailAlloc_2950_, 9, v_canon_2939_);
lean_ctor_set(v_reuseFailAlloc_2950_, 10, v_instanceOverrides_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_2950_, sizeof(void*)*11, v_debug_2941_);
v___x_2946_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_st_ref_put(v_a_2880_, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2928_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2955_, lean_object* v_ctx_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2955_, v_ctx_2956_, v_a_2957_);
lean_dec(v_a_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2960_, lean_object* v_k_2961_, lean_object* v_ctx_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2961_, v_ctx_2962_, v_a_2964_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_k_2972_, lean_object* v_ctx_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2971_, v_k_2972_, v_ctx_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2982_){
_start:
{
lean_object* v_config_2983_; lean_object* v_sharedExprs_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3001_; 
v_config_2983_ = lean_ctor_get(v_ctx_2982_, 1);
v_sharedExprs_2984_ = lean_ctor_get(v_ctx_2982_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_ctx_2982_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2986_ = v_ctx_2982_;
v_isShared_2987_ = v_isSharedCheck_3001_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_config_2983_);
lean_inc(v_sharedExprs_2984_);
lean_dec(v_ctx_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3001_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
uint8_t v_verbose_2988_; uint8_t v_enforceUnfoldReducible_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3000_; 
v_verbose_2988_ = lean_ctor_get_uint8(v_config_2983_, 0);
v_enforceUnfoldReducible_2989_ = lean_ctor_get_uint8(v_config_2983_, 1);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_config_2983_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2991_ = v_config_2983_;
v_isShared_2992_ = v_isSharedCheck_3000_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v_config_2983_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3000_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint8_t v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = 0;
if (v_isShared_2992_ == 0)
{
v___x_2995_ = v___x_2991_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, 0, v_verbose_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, 1, v_enforceUnfoldReducible_2989_);
v___x_2995_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
lean_ctor_set_uint8(v___x_2995_, 2, v___x_2993_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v___x_2995_);
v___x_2997_ = v___x_2986_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_sharedExprs_2984_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v___f_3005_; lean_object* v___x_3006_; 
v___f_3005_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_3006_ = lean_apply_3(v_inst_3003_, lean_box(0), v___f_3005_, v_x_3004_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_3007_, lean_object* v_00_u03b1_3008_, lean_object* v_inst_3009_, lean_object* v_x_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_3009_, v_x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_3012_){
_start:
{
lean_object* v_config_3013_; lean_object* v_sharedExprs_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3030_; 
v_config_3013_ = lean_ctor_get(v_ctx_3012_, 1);
v_sharedExprs_3014_ = lean_ctor_get(v_ctx_3012_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_ctx_3012_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3016_ = v_ctx_3012_;
v_isShared_3017_ = v_isSharedCheck_3030_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_config_3013_);
lean_inc(v_sharedExprs_3014_);
lean_dec(v_ctx_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3030_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
uint8_t v_verbose_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3029_; 
v_verbose_3018_ = lean_ctor_get_uint8(v_config_3013_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_config_3013_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3020_ = v_config_3013_;
v_isShared_3021_ = v_isSharedCheck_3029_;
goto v_resetjp_3019_;
}
else
{
lean_dec(v_config_3013_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3029_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
uint8_t v___x_3022_; lean_object* v___x_3024_; 
v___x_3022_ = 0;
if (v_isShared_3021_ == 0)
{
v___x_3024_ = v___x_3020_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3028_, 0, v_verbose_3018_);
v___x_3024_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
lean_ctor_set_uint8(v___x_3024_, 1, v___x_3022_);
lean_ctor_set_uint8(v___x_3024_, 2, v___x_3022_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v___x_3024_);
v___x_3026_ = v___x_3016_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_sharedExprs_3014_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_3032_, lean_object* v_x_3033_){
_start:
{
lean_object* v___f_3034_; lean_object* v___x_3035_; 
v___f_3034_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_3035_ = lean_apply_3(v_inst_3032_, lean_box(0), v___f_3034_, v_x_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_3036_, lean_object* v_00_u03b1_3037_, lean_object* v_inst_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_3038_, v_x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v_config_3045_; lean_object* v_env_3046_; uint8_t v_enforceUnfoldReducible_3047_; uint8_t v_enforceFoldProjs_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3044_ = lean_st_ref_get(v_a_3042_);
v_config_3045_ = lean_ctor_get(v_a_3041_, 1);
v_env_3046_ = lean_ctor_get(v___x_3044_, 0);
lean_inc_ref(v_env_3046_);
lean_dec(v___x_3044_);
v_enforceUnfoldReducible_3047_ = lean_ctor_get_uint8(v_config_3045_, 1);
v_enforceFoldProjs_3048_ = lean_ctor_get_uint8(v_config_3045_, 2);
v___x_3049_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3049_, 0, v_env_3046_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1, v_enforceUnfoldReducible_3047_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1 + 1, v_enforceFoldProjs_3048_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3055_, v_a_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_config_3078_; uint8_t v_enforceUnfoldReducible_3079_; uint8_t v_enforceFoldProjs_3080_; lean_object* v_e_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v_e_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; 
v_config_3078_ = lean_ctor_get(v_a_3072_, 1);
v_enforceUnfoldReducible_3079_ = lean_ctor_get_uint8(v_config_3078_, 1);
v_enforceFoldProjs_3080_ = lean_ctor_get_uint8(v_config_3078_, 2);
if (v_enforceUnfoldReducible_3079_ == 0)
{
v_e_3090_ = v_e_3071_;
v___y_3091_ = v_a_3073_;
v___y_3092_ = v_a_3074_;
v___y_3093_ = v_a_3075_;
v___y_3094_ = v_a_3076_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3071_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_e_3090_ = v_a_3098_;
v___y_3091_ = v_a_3073_;
v___y_3092_ = v_a_3074_;
v___y_3093_ = v_a_3075_;
v___y_3094_ = v_a_3076_;
goto v___jp_3089_;
}
else
{
return v___x_3097_;
}
}
v___jp_3081_:
{
if (v_enforceUnfoldReducible_3079_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_e_3082_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3088_;
}
}
v___jp_3089_:
{
if (v_enforceFoldProjs_3080_ == 0)
{
v_e_3082_ = v_e_3090_;
v___y_3083_ = v___y_3091_;
v___y_3084_ = v___y_3092_;
v___y_3085_ = v___y_3093_;
v___y_3086_ = v___y_3094_;
goto v___jp_3081_;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Meta_Sym_foldProjs(v_e_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v_e_3082_ = v_a_3096_;
v___y_3083_ = v___y_3091_;
v___y_3084_ = v___y_3092_;
v___y_3085_ = v___y_3093_;
v___y_3086_ = v___y_3094_;
goto v___jp_3081_;
}
else
{
return v___x_3095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec_ref(v_a_3100_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3107_, v_a_3108_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec_ref(v_a_3119_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
return v_res_3124_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_instMonadEIO(lean_box(0));
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v_toApplicative_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3203_; 
v___x_3138_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3139_ = l_StateRefT_x27_instMonad___redArg(v___x_3138_);
v_toApplicative_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___x_3139_, 1);
lean_dec(v_unused_3204_);
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3203_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_toApplicative_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3203_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_toFunctor_3144_; lean_object* v_toSeq_3145_; lean_object* v_toSeqLeft_3146_; lean_object* v_toSeqRight_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3201_; 
v_toFunctor_3144_ = lean_ctor_get(v_toApplicative_3140_, 0);
v_toSeq_3145_ = lean_ctor_get(v_toApplicative_3140_, 2);
v_toSeqLeft_3146_ = lean_ctor_get(v_toApplicative_3140_, 3);
v_toSeqRight_3147_ = lean_ctor_get(v_toApplicative_3140_, 4);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_toApplicative_3140_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; 
v_unused_3202_ = lean_ctor_get(v_toApplicative_3140_, 1);
lean_dec(v_unused_3202_);
v___x_3149_ = v_toApplicative_3140_;
v_isShared_3150_ = v_isSharedCheck_3201_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_toSeqRight_3147_);
lean_inc(v_toSeqLeft_3146_);
lean_inc(v_toSeq_3145_);
lean_inc(v_toFunctor_3144_);
lean_dec(v_toApplicative_3140_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3201_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___f_3158_; lean_object* v___x_3160_; 
v___f_3151_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3152_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3144_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toFunctor_3144_);
v___f_3154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3154_, 0, v_toFunctor_3144_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___f_3153_);
lean_ctor_set(v___x_3155_, 1, v___f_3154_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toSeqRight_3147_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toSeqLeft_3146_);
v___f_3158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3158_, 0, v_toSeq_3145_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 4, v___f_3156_);
lean_ctor_set(v___x_3149_, 3, v___f_3157_);
lean_ctor_set(v___x_3149_, 2, v___f_3158_);
lean_ctor_set(v___x_3149_, 1, v___f_3151_);
lean_ctor_set(v___x_3149_, 0, v___x_3155_);
v___x_3160_ = v___x_3149_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___f_3151_);
lean_ctor_set(v_reuseFailAlloc_3200_, 2, v___f_3158_);
lean_ctor_set(v_reuseFailAlloc_3200_, 3, v___f_3157_);
lean_ctor_set(v_reuseFailAlloc_3200_, 4, v___f_3156_);
v___x_3160_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3162_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 1, v___f_3152_);
lean_ctor_set(v___x_3142_, 0, v___x_3160_);
v___x_3162_ = v___x_3142_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___f_3152_);
v___x_3162_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v_toApplicative_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3197_; 
v___x_3163_ = l_StateRefT_x27_instMonad___redArg(v___x_3162_);
v_toApplicative_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; 
v_unused_3198_ = lean_ctor_get(v___x_3163_, 1);
lean_dec(v_unused_3198_);
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3197_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_toApplicative_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3197_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v_toFunctor_3168_; lean_object* v_toSeq_3169_; lean_object* v_toSeqLeft_3170_; lean_object* v_toSeqRight_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3195_; 
v_toFunctor_3168_ = lean_ctor_get(v_toApplicative_3164_, 0);
v_toSeq_3169_ = lean_ctor_get(v_toApplicative_3164_, 2);
v_toSeqLeft_3170_ = lean_ctor_get(v_toApplicative_3164_, 3);
v_toSeqRight_3171_ = lean_ctor_get(v_toApplicative_3164_, 4);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_toApplicative_3164_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v_toApplicative_3164_, 1);
lean_dec(v_unused_3196_);
v___x_3173_ = v_toApplicative_3164_;
v_isShared_3174_ = v_isSharedCheck_3195_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_toSeqRight_3171_);
lean_inc(v_toSeqLeft_3170_);
lean_inc(v_toSeq_3169_);
lean_inc(v_toFunctor_3168_);
lean_dec(v_toApplicative_3164_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3195_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___x_3184_; 
v___f_3175_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3176_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3168_);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toFunctor_3168_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toFunctor_3168_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___f_3177_);
lean_ctor_set(v___x_3179_, 1, v___f_3178_);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toSeqRight_3171_);
v___f_3181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3181_, 0, v_toSeqLeft_3170_);
v___f_3182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3182_, 0, v_toSeq_3169_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 4, v___f_3180_);
lean_ctor_set(v___x_3173_, 3, v___f_3181_);
lean_ctor_set(v___x_3173_, 2, v___f_3182_);
lean_ctor_set(v___x_3173_, 1, v___f_3175_);
lean_ctor_set(v___x_3173_, 0, v___x_3179_);
v___x_3184_ = v___x_3173_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___f_3175_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v___f_3182_);
lean_ctor_set(v_reuseFailAlloc_3194_, 3, v___f_3181_);
lean_ctor_set(v_reuseFailAlloc_3194_, 4, v___f_3180_);
v___x_3184_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3186_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 1, v___f_3176_);
lean_ctor_set(v___x_3166_, 0, v___x_3184_);
v___x_3186_ = v___x_3166_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___f_3176_);
v___x_3186_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___f_3190_; lean_object* v___x_909__overap_3191_; lean_object* v___x_3192_; 
v___x_3187_ = l_StateRefT_x27_instMonad___redArg(v___x_3186_);
v___x_3188_ = l_Lean_instInhabitedExpr;
v___x_3189_ = l_instInhabitedOfMonad___redArg(v___x_3187_, v___x_3188_);
v___f_3190_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3190_, 0, v___x_3189_);
v___x_909__overap_3191_ = lean_panic_fn_borrowed(v___f_3190_, v_msg_3130_);
lean_dec_ref(v___f_3190_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
v___x_3192_ = lean_apply_7(v___x_909__overap_3191_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, lean_box(0));
return v___x_3192_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3214_, lean_object* v_vals_3215_, lean_object* v_i_3216_, lean_object* v_k_3217_){
_start:
{
lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = lean_array_get_size(v_keys_3214_);
v___x_3219_ = lean_nat_dec_lt(v_i_3216_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_dec(v_i_3216_);
v___x_3220_ = lean_box(0);
return v___x_3220_;
}
else
{
lean_object* v_k_x27_3221_; uint8_t v___x_3222_; 
v_k_x27_3221_ = lean_array_fget_borrowed(v_keys_3214_, v_i_3216_);
v___x_3222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3217_, v_k_x27_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_nat_add(v_i_3216_, v___x_3223_);
lean_dec(v_i_3216_);
v_i_3216_ = v___x_3224_;
goto _start;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_array_fget_borrowed(v_vals_3215_, v_i_3216_);
lean_dec(v_i_3216_);
lean_inc(v___x_3226_);
lean_inc(v_k_x27_3221_);
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v_k_x27_3221_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3229_, lean_object* v_vals_3230_, lean_object* v_i_3231_, lean_object* v_k_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3229_, v_vals_3230_, v_i_3231_, v_k_3232_);
lean_dec_ref(v_k_3232_);
lean_dec_ref(v_vals_3230_);
lean_dec_ref(v_keys_3229_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3234_, size_t v_x_3235_, lean_object* v_x_3236_){
_start:
{
if (lean_obj_tag(v_x_3234_) == 0)
{
lean_object* v_es_3237_; lean_object* v___x_3238_; size_t v___x_3239_; size_t v___x_3240_; lean_object* v_j_3241_; lean_object* v___x_3242_; 
v_es_3237_ = lean_ctor_get(v_x_3234_, 0);
v___x_3238_ = lean_box(2);
v___x_3239_ = ((size_t)31ULL);
v___x_3240_ = lean_usize_land(v_x_3235_, v___x_3239_);
v_j_3241_ = lean_usize_to_nat(v___x_3240_);
v___x_3242_ = lean_array_get_borrowed(v___x_3238_, v_es_3237_, v_j_3241_);
lean_dec(v_j_3241_);
switch(lean_obj_tag(v___x_3242_))
{
case 0:
{
lean_object* v_key_3243_; lean_object* v_val_3244_; uint8_t v___x_3245_; 
v_key_3243_ = lean_ctor_get(v___x_3242_, 0);
v_val_3244_ = lean_ctor_get(v___x_3242_, 1);
v___x_3245_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3236_, v_key_3243_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_box(0);
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_inc(v_val_3244_);
lean_inc(v_key_3243_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_key_3243_);
lean_ctor_set(v___x_3247_, 1, v_val_3244_);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
return v___x_3248_;
}
}
case 1:
{
lean_object* v_node_3249_; size_t v___x_3250_; size_t v___x_3251_; 
v_node_3249_ = lean_ctor_get(v___x_3242_, 0);
v___x_3250_ = ((size_t)5ULL);
v___x_3251_ = lean_usize_shift_right(v_x_3235_, v___x_3250_);
v_x_3234_ = v_node_3249_;
v_x_3235_ = v___x_3251_;
goto _start;
}
default: 
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_box(0);
return v___x_3253_;
}
}
}
else
{
lean_object* v_ks_3254_; lean_object* v_vs_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_ks_3254_ = lean_ctor_get(v_x_3234_, 0);
v_vs_3255_ = lean_ctor_get(v_x_3234_, 1);
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3254_, v_vs_3255_, v___x_3256_, v_x_3236_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_){
_start:
{
size_t v_x_1226__boxed_3261_; lean_object* v_res_3262_; 
v_x_1226__boxed_3261_ = lean_unbox_usize(v_x_3259_);
lean_dec(v_x_3259_);
v_res_3262_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3258_, v_x_1226__boxed_3261_, v_x_3260_);
lean_dec_ref(v_x_3260_);
lean_dec_ref(v_x_3258_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3263_, lean_object* v_x_3264_){
_start:
{
uint64_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3264_);
v___x_3266_ = lean_uint64_to_usize(v___x_3265_);
v___x_3267_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3263_, v___x_3266_, v_x_3264_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3268_, v_x_3269_);
lean_dec_ref(v_x_3269_);
lean_dec_ref(v_x_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3271_, lean_object* v_cache_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3274_, v_e_3271_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_cache_3272_);
lean_ctor_set(v___x_3276_, 1, v___y_3274_);
v___x_3277_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3271_, v___y_3273_, v___x_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3287_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 1);
v_a_3279_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3281_ = v___x_3277_;
v_isShared_3282_ = v_isSharedCheck_3287_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3278_);
lean_inc(v_a_3279_);
lean_dec(v___x_3277_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3287_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_set_3283_; lean_object* v___x_3285_; 
v_set_3283_ = lean_ctor_get(v_a_3278_, 1);
lean_inc_ref(v_set_3283_);
lean_dec(v_a_3278_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v_set_3283_);
v___x_3285_ = v___x_3281_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3279_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_set_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3297_; 
v_a_3288_ = lean_ctor_get(v___x_3277_, 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3277_, 0);
lean_dec(v_unused_3298_);
v___x_3290_ = v___x_3277_;
v_isShared_3291_ = v_isSharedCheck_3297_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3277_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3297_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v_map_3292_; lean_object* v_set_3293_; lean_object* v___x_3295_; 
v_map_3292_ = lean_ctor_get(v_a_3288_, 0);
lean_inc_ref(v_map_3292_);
v_set_3293_ = lean_ctor_get(v_a_3288_, 1);
lean_inc_ref(v_set_3293_);
lean_dec(v_a_3288_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 1, v_set_3293_);
lean_ctor_set(v___x_3290_, 0, v_map_3292_);
v___x_3295_ = v___x_3290_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_map_3292_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_set_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_val_3299_; lean_object* v_fst_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref(v_cache_3272_);
lean_dec_ref(v_e_3271_);
v_val_3299_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v___x_3275_, 1);
v_fst_3300_ = lean_ctor_get(v_val_3299_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_val_3299_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; 
v_unused_3308_ = lean_ctor_get(v_val_3299_, 1);
lean_dec(v_unused_3308_);
v___x_3302_ = v_val_3299_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_fst_3300_);
lean_dec(v_val_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v___y_3274_);
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_fst_3300_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___y_3274_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3309_, lean_object* v_cache_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3309_, v_cache_3310_, v___y_3311_, v___y_3312_);
lean_dec_ref(v___y_3311_);
return v_res_3313_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3315_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_3316_ = lean_unsigned_to_nat(16u);
v___x_3317_ = lean_unsigned_to_nat(396u);
v___x_3318_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3319_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3320_ = l_mkPanicMessageWithDecl(v___x_3319_, v___x_3318_, v___x_3317_, v___x_3316_, v___x_3315_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3321_, lean_object* v_cache_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___x_3330_; lean_object* v_env_3331_; lean_object* v___f_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3346_; 
v___x_3330_ = lean_st_ref_get(v_a_3328_);
v_env_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc_ref(v_env_3331_);
lean_dec(v___x_3330_);
v___f_3332_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3332_, 0, v_e_3321_);
lean_closure_set(v___f_3332_, 1, v_cache_3322_);
v___x_3333_ = 0;
v___x_3334_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3334_, 0, v_env_3331_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*1, v___x_3333_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*1 + 1, v___x_3333_);
v___x_3335_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3332_, v___x_3334_, v_a_3324_);
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3346_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3346_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
if (lean_obj_tag(v_a_3336_) == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec_ref_known(v_a_3336_, 1);
lean_del_object(v___x_3338_);
v___x_3340_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3341_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3340_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
return v___x_3341_;
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; 
v_a_3342_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v_a_3336_, 1);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_a_3342_);
v___x_3344_ = v___x_3338_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3347_, lean_object* v_cache_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3347_, v_cache_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3358_, v_x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3361_, lean_object* v_x_3362_, lean_object* v_x_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3361_, v_x_3362_, v_x_3363_);
lean_dec_ref(v_x_3363_);
lean_dec_ref(v_x_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3365_, lean_object* v_x_3366_, size_t v_x_3367_, lean_object* v_x_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3366_, v_x_3367_, v_x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_, lean_object* v_x_3373_){
_start:
{
size_t v_x_1431__boxed_3374_; lean_object* v_res_3375_; 
v_x_1431__boxed_3374_ = lean_unbox_usize(v_x_3372_);
lean_dec(v_x_3372_);
v_res_3375_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3370_, v_x_3371_, v_x_1431__boxed_3374_, v_x_3373_);
lean_dec_ref(v_x_3373_);
lean_dec_ref(v_x_3371_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3376_, lean_object* v_keys_3377_, lean_object* v_vals_3378_, lean_object* v_heq_3379_, lean_object* v_i_3380_, lean_object* v_k_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3377_, v_vals_3378_, v_i_3380_, v_k_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3383_, lean_object* v_keys_3384_, lean_object* v_vals_3385_, lean_object* v_heq_3386_, lean_object* v_i_3387_, lean_object* v_k_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3383_, v_keys_3384_, v_vals_3385_, v_heq_3386_, v_i_3387_, v_k_3388_);
lean_dec_ref(v_k_3388_);
lean_dec_ref(v_vals_3385_);
lean_dec_ref(v_keys_3384_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_ref_3396_; lean_object* v___x_3397_; lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3406_; 
v_ref_3396_ = lean_ctor_get(v___y_3393_, 5);
v___x_3397_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
lean_inc(v_ref_3396_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_ref_3396_);
lean_ctor_set(v___x_3402_, 1, v_a_3398_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 1);
lean_ctor_set(v___x_3400_, 0, v___x_3402_);
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
return v_res_3413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3416_ = l_Lean_stringToMessageData(v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3417_, lean_object* v_cache_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; uint8_t v___x_3436_; 
v___x_3436_ = l_Lean_Expr_hasLooseBVars(v_e_3417_);
if (v___x_3436_ == 0)
{
v___y_3427_ = v_a_3419_;
v___y_3428_ = v_a_3420_;
v___y_3429_ = v_a_3421_;
v___y_3430_ = v_a_3422_;
v___y_3431_ = v_a_3423_;
v___y_3432_ = v_a_3424_;
goto v___jp_3426_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v_cache_3418_);
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3438_ = l_Lean_indentExpr(v_e_3417_);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3439_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
v___jp_3426_:
{
lean_object* v___x_3433_; 
v___x_3433_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3417_, v___y_3427_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3434_, v_cache_3418_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3435_;
}
else
{
lean_dec_ref(v_cache_3418_);
return v___x_3433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3449_, lean_object* v_cache_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3449_, v_cache_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3459_, lean_object* v_msg_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3460_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3469_, lean_object* v_msg_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3469_, v_msg_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3479_, lean_object* v___x_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3482_, v_e_3479_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3480_);
lean_ctor_set(v___x_3484_, 1, v___y_3482_);
v___x_3485_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3479_, v___y_3481_, v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3495_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 1);
v_a_3487_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3489_ = v___x_3485_;
v_isShared_3490_ = v_isSharedCheck_3495_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3486_);
lean_inc(v_a_3487_);
lean_dec(v___x_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3495_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_set_3491_; lean_object* v___x_3493_; 
v_set_3491_ = lean_ctor_get(v_a_3486_, 1);
lean_inc_ref(v_set_3491_);
lean_dec(v_a_3486_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_set_3491_);
v___x_3493_ = v___x_3489_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3487_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_set_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3505_; 
v_a_3496_ = lean_ctor_get(v___x_3485_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; 
v_unused_3506_ = lean_ctor_get(v___x_3485_, 0);
lean_dec(v_unused_3506_);
v___x_3498_ = v___x_3485_;
v_isShared_3499_ = v_isSharedCheck_3505_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3485_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3505_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_map_3500_; lean_object* v_set_3501_; lean_object* v___x_3503_; 
v_map_3500_ = lean_ctor_get(v_a_3496_, 0);
lean_inc_ref(v_map_3500_);
v_set_3501_ = lean_ctor_get(v_a_3496_, 1);
lean_inc_ref(v_set_3501_);
lean_dec(v_a_3496_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v_set_3501_);
lean_ctor_set(v___x_3498_, 0, v_map_3500_);
v___x_3503_ = v___x_3498_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_map_3500_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_set_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v_val_3507_; lean_object* v_fst_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v___x_3480_);
lean_dec_ref(v_e_3479_);
v_val_3507_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_val_3507_);
lean_dec_ref_known(v___x_3483_, 1);
v_fst_3508_ = lean_ctor_get(v_val_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_val_3507_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v_val_3507_, 1);
lean_dec(v_unused_3516_);
v___x_3510_ = v_val_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_fst_3508_);
lean_dec(v_val_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___y_3482_);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___y_3482_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3517_, lean_object* v___x_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3517_, v___x_3518_, v___y_3519_, v___y_3520_);
lean_dec_ref(v___y_3519_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___f_3533_; lean_object* v___x_3534_; lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3545_; 
v___x_3530_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3523_, v_a_3528_);
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref(v___x_3530_);
v___x_3532_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
lean_inc_ref(v_e_3522_);
v___f_3533_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3533_, 0, v_e_3522_);
lean_closure_set(v___f_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3533_, v_a_3531_, v_a_3524_);
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3545_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3545_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
if (lean_obj_tag(v_a_3535_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3540_; 
lean_del_object(v___x_3537_);
v_a_3539_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v_a_3535_, 1);
v___x_3540_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3522_, v_a_3539_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
return v___x_3540_;
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; 
lean_dec_ref(v_e_3522_);
v_a_3541_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v_a_3535_, 1);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_a_3541_);
v___x_3543_ = v___x_3537_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Meta_Sym_shareCommon(v_e_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3555_, v___y_3556_, v___y_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3559_, v___y_3560_, v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v___x_3571_; lean_object* v_a_3572_; lean_object* v___f_3573_; lean_object* v___x_3574_; lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3585_; 
v___x_3571_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3564_, v_a_3569_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref(v___x_3571_);
lean_inc_ref(v_e_3563_);
v___f_3573_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3573_, 0, v_e_3563_);
v___x_3574_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3573_, v_a_3572_, v_a_3565_);
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3585_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3585_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
if (lean_obj_tag(v_a_3575_) == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref_known(v_a_3575_, 1);
lean_del_object(v___x_3577_);
v___x_3579_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_3580_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3563_, v___x_3579_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
return v___x_3580_;
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; 
lean_dec_ref(v_e_3563_);
v_a_3581_ = lean_ctor_get(v_a_3575_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v_a_3575_, 1);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v_a_3581_);
v___x_3583_ = v___x_3577_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Meta_Sym_share(v_e_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3613_){
_start:
{
lean_object* v___x_3615_; uint8_t v_debug_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3615_ = lean_st_ref_get(v_a_3613_);
v_debug_3616_ = lean_ctor_get_uint8(v___x_3615_, sizeof(void*)*11);
lean_dec(v___x_3615_);
v___x_3617_ = lean_box(v_debug_3616_);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3619_);
lean_dec(v_a_3619_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3629_; uint8_t v_debug_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3629_ = lean_st_ref_get(v_a_3623_);
v_debug_3630_ = lean_ctor_get_uint8(v___x_3629_, sizeof(void*)*11);
lean_dec(v___x_3629_);
v___x_3631_ = lean_box(v_debug_3630_);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3641_){
_start:
{
lean_object* v_config_3643_; lean_object* v___x_3644_; 
v_config_3643_ = lean_ctor_get(v_a_3641_, 1);
lean_inc_ref(v_config_3643_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_config_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3645_);
lean_dec_ref(v_a_3645_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3648_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_Meta_Sym_getConfig(v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_a_3657_);
lean_dec_ref(v_a_3656_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3664_, lean_object* v_msg_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_ref_3671_; lean_object* v___x_3672_; lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3717_; 
v_ref_3671_ = lean_ctor_get(v___y_3668_, 5);
v___x_3672_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3717_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3717_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v_traceState_3678_; lean_object* v_env_3679_; lean_object* v_nextMacroScope_3680_; lean_object* v_ngen_3681_; lean_object* v_auxDeclNGen_3682_; lean_object* v_cache_3683_; lean_object* v_messages_3684_; lean_object* v_infoState_3685_; lean_object* v_snapshotTasks_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3716_; 
v___x_3677_ = lean_st_ref_take(v___y_3669_);
v_traceState_3678_ = lean_ctor_get(v___x_3677_, 4);
v_env_3679_ = lean_ctor_get(v___x_3677_, 0);
v_nextMacroScope_3680_ = lean_ctor_get(v___x_3677_, 1);
v_ngen_3681_ = lean_ctor_get(v___x_3677_, 2);
v_auxDeclNGen_3682_ = lean_ctor_get(v___x_3677_, 3);
v_cache_3683_ = lean_ctor_get(v___x_3677_, 5);
v_messages_3684_ = lean_ctor_get(v___x_3677_, 6);
v_infoState_3685_ = lean_ctor_get(v___x_3677_, 7);
v_snapshotTasks_3686_ = lean_ctor_get(v___x_3677_, 8);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3688_ = v___x_3677_;
v_isShared_3689_ = v_isSharedCheck_3716_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_snapshotTasks_3686_);
lean_inc(v_infoState_3685_);
lean_inc(v_messages_3684_);
lean_inc(v_cache_3683_);
lean_inc(v_traceState_3678_);
lean_inc(v_auxDeclNGen_3682_);
lean_inc(v_ngen_3681_);
lean_inc(v_nextMacroScope_3680_);
lean_inc(v_env_3679_);
lean_dec(v___x_3677_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3716_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
uint64_t v_tid_3690_; lean_object* v_traces_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3715_; 
v_tid_3690_ = lean_ctor_get_uint64(v_traceState_3678_, sizeof(void*)*1);
v_traces_3691_ = lean_ctor_get(v_traceState_3678_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v_traceState_3678_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3693_ = v_traceState_3678_;
v_isShared_3694_ = v_isSharedCheck_3715_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_traces_3691_);
lean_dec(v_traceState_3678_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3715_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3695_; double v___x_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3695_ = lean_box(0);
v___x_3696_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3697_ = 0;
v___x_3698_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3699_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3699_, 0, v_cls_3664_);
lean_ctor_set(v___x_3699_, 1, v___x_3695_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
lean_ctor_set_float(v___x_3699_, sizeof(void*)*3, v___x_3696_);
lean_ctor_set_float(v___x_3699_, sizeof(void*)*3 + 8, v___x_3696_);
lean_ctor_set_uint8(v___x_3699_, sizeof(void*)*3 + 16, v___x_3697_);
v___x_3700_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3701_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v_a_3673_);
lean_ctor_set(v___x_3701_, 2, v___x_3700_);
lean_inc(v_ref_3671_);
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v_ref_3671_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = l_Lean_PersistentArray_push___redArg(v_traces_3691_, v___x_3702_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3703_);
v___x_3705_ = v___x_3693_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3703_);
lean_ctor_set_uint64(v_reuseFailAlloc_3714_, sizeof(void*)*1, v_tid_3690_);
v___x_3705_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 4, v___x_3705_);
v___x_3707_ = v___x_3688_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_env_3679_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_nextMacroScope_3680_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_ngen_3681_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_auxDeclNGen_3682_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3713_, 5, v_cache_3683_);
lean_ctor_set(v_reuseFailAlloc_3713_, 6, v_messages_3684_);
lean_ctor_set(v_reuseFailAlloc_3713_, 7, v_infoState_3685_);
lean_ctor_set(v_reuseFailAlloc_3713_, 8, v_snapshotTasks_3686_);
v___x_3707_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3708_ = lean_st_ref_put(v___y_3669_, v___x_3707_);
v___x_3709_ = lean_box(0);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3709_);
v___x_3711_ = v___x_3675_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3718_, lean_object* v_msg_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3718_, v_msg_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
return v_res_3725_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3729_; uint8_t v___x_3730_; double v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3729_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3730_ = 1;
v___x_3731_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3732_ = lean_box(0);
v___x_3733_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3734_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
lean_ctor_set(v___x_3734_, 1, v___x_3732_);
lean_ctor_set(v___x_3734_, 2, v___x_3729_);
lean_ctor_set_float(v___x_3734_, sizeof(void*)*3, v___x_3731_);
lean_ctor_set_float(v___x_3734_, sizeof(void*)*3 + 8, v___x_3731_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*3 + 16, v___x_3730_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v___x_3746_; lean_object* v_a_3747_; lean_object* v___x_3748_; lean_object* v_share_3749_; lean_object* v_maxFVar_3750_; lean_object* v_proofInstInfo_3751_; lean_object* v_inferType_3752_; lean_object* v_getLevel_3753_; lean_object* v_congrInfo_3754_; lean_object* v_defEqI_3755_; lean_object* v_extensions_3756_; lean_object* v_issues_3757_; lean_object* v_canon_3758_; lean_object* v_instanceOverrides_3759_; uint8_t v_debug_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3779_; 
v___x_3746_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3735_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref(v___x_3746_);
v___x_3748_ = lean_st_ref_take(v_a_3737_);
v_share_3749_ = lean_ctor_get(v___x_3748_, 0);
v_maxFVar_3750_ = lean_ctor_get(v___x_3748_, 1);
v_proofInstInfo_3751_ = lean_ctor_get(v___x_3748_, 2);
v_inferType_3752_ = lean_ctor_get(v___x_3748_, 3);
v_getLevel_3753_ = lean_ctor_get(v___x_3748_, 4);
v_congrInfo_3754_ = lean_ctor_get(v___x_3748_, 5);
v_defEqI_3755_ = lean_ctor_get(v___x_3748_, 6);
v_extensions_3756_ = lean_ctor_get(v___x_3748_, 7);
v_issues_3757_ = lean_ctor_get(v___x_3748_, 8);
v_canon_3758_ = lean_ctor_get(v___x_3748_, 9);
v_instanceOverrides_3759_ = lean_ctor_get(v___x_3748_, 10);
v_debug_3760_ = lean_ctor_get_uint8(v___x_3748_, sizeof(void*)*11);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3762_ = v___x_3748_;
v_isShared_3763_ = v_isSharedCheck_3779_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_instanceOverrides_3759_);
lean_inc(v_canon_3758_);
lean_inc(v_issues_3757_);
lean_inc(v_extensions_3756_);
lean_inc(v_defEqI_3755_);
lean_inc(v_congrInfo_3754_);
lean_inc(v_getLevel_3753_);
lean_inc(v_inferType_3752_);
lean_inc(v_proofInstInfo_3751_);
lean_inc(v_maxFVar_3750_);
lean_inc(v_share_3749_);
lean_dec(v___x_3748_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3779_;
goto v_resetjp_3761_;
}
v___jp_3743_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_box(0);
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3764_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3765_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3747_);
v___x_3766_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v_a_3747_);
lean_ctor_set(v___x_3766_, 2, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set(v___x_3767_, 1, v_issues_3757_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 8, v___x_3767_);
v___x_3769_ = v___x_3762_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_share_3749_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_maxFVar_3750_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_proofInstInfo_3751_);
lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_inferType_3752_);
lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_getLevel_3753_);
lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_congrInfo_3754_);
lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_defEqI_3755_);
lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_extensions_3756_);
lean_ctor_set(v_reuseFailAlloc_3778_, 8, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_canon_3758_);
lean_ctor_set(v_reuseFailAlloc_3778_, 10, v_instanceOverrides_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3778_, sizeof(void*)*11, v_debug_3760_);
v___x_3769_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v_options_3771_; uint8_t v_hasTrace_3772_; 
v___x_3770_ = lean_st_ref_put(v_a_3737_, v___x_3769_);
v_options_3771_ = lean_ctor_get(v_a_3740_, 2);
v_hasTrace_3772_ = lean_ctor_get_uint8(v_options_3771_, sizeof(void*)*1);
if (v_hasTrace_3772_ == 0)
{
lean_dec(v_a_3747_);
goto v___jp_3743_;
}
else
{
lean_object* v_inheritedTraceOptions_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_inheritedTraceOptions_3773_ = lean_ctor_get(v_a_3740_, 13);
v___x_3774_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3775_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_3776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3773_, v_options_3771_, v___x_3775_);
if (v___x_3776_ == 0)
{
lean_dec(v_a_3747_);
goto v___jp_3743_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3774_, v_a_3747_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
return v___x_3777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Meta_Sym_reportIssue(v_msg_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3789_, lean_object* v_msg_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3789_, v_msg_3790_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3799_, lean_object* v_msg_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3799_, v_msg_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v___x_3817_; lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3828_; 
v___x_3817_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3810_);
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3828_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3828_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
uint8_t v_verbose_3822_; 
v_verbose_3822_ = lean_ctor_get_uint8(v_a_3818_, 0);
lean_dec(v_a_3818_);
if (v_verbose_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_dec_ref(v_msg_3809_);
v___x_3823_ = lean_box(0);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3823_);
v___x_3825_ = v___x_3820_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
else
{
lean_object* v___x_3827_; 
lean_del_object(v___x_3820_);
v___x_3827_ = l_Lean_Meta_Sym_reportIssue(v_msg_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
return v___x_3827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
return v_res_3837_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3854_ = l_String_toRawSubstring_x27(v___x_3853_);
return v___x_3854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3893_ = l_String_toRawSubstring_x27(v___x_3892_);
return v___x_3893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3906_ = l_String_toRawSubstring_x27(v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_msg_3933_; lean_object* v_quotContext_3934_; lean_object* v_currMacroScope_3935_; lean_object* v_ref_3936_; lean_object* v___y_3937_; lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
lean_inc(v_s_3929_);
v___x_3952_ = l_Lean_Syntax_getKind(v_s_3929_);
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3954_ = lean_name_eq(v___x_3952_, v___x_3953_);
lean_dec(v___x_3952_);
if (v___x_3954_ == 0)
{
lean_object* v_quotContext_3955_; lean_object* v_currMacroScope_3956_; lean_object* v_ref_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_quotContext_3955_ = lean_ctor_get(v_a_3930_, 1);
v_currMacroScope_3956_ = lean_ctor_get(v_a_3930_, 2);
v_ref_3957_ = lean_ctor_get(v_a_3930_, 5);
v___x_3958_ = l_Lean_SourceInfo_fromRef(v_ref_3957_, v___x_3954_);
v___x_3959_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3960_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3958_, 8);
v___x_3962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3958_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3964_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3965_ = lean_box(0);
lean_inc_n(v_currMacroScope_3956_, 3);
lean_inc_n(v_quotContext_3955_, 3);
v___x_3966_ = l_Lean_addMacroScope(v_quotContext_3955_, v___x_3965_, v_currMacroScope_3956_);
v___x_3967_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3968_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3958_);
lean_ctor_set(v___x_3968_, 1, v___x_3964_);
lean_ctor_set(v___x_3968_, 2, v___x_3966_);
lean_ctor_set(v___x_3968_, 3, v___x_3967_);
v___x_3969_ = l_Lean_Syntax_node1(v___x_3958_, v___x_3963_, v___x_3968_);
v___x_3970_ = l_Lean_Syntax_node2(v___x_3958_, v___x_3960_, v___x_3962_, v___x_3969_);
v___x_3971_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_3972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3958_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3974_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_3975_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_3976_ = l_Lean_addMacroScope(v_quotContext_3955_, v___x_3975_, v_currMacroScope_3956_);
v___x_3977_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_3978_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3958_);
lean_ctor_set(v___x_3978_, 1, v___x_3974_);
lean_ctor_set(v___x_3978_, 2, v___x_3976_);
lean_ctor_set(v___x_3978_, 3, v___x_3977_);
v___x_3979_ = l_Lean_Syntax_node1(v___x_3958_, v___x_3973_, v___x_3978_);
v___x_3980_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_3981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3958_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = l_Lean_Syntax_node5(v___x_3958_, v___x_3959_, v___x_3970_, v_s_3929_, v___x_3972_, v___x_3979_, v___x_3981_);
v_msg_3933_ = v___x_3982_;
v_quotContext_3934_ = v_quotContext_3955_;
v_currMacroScope_3935_ = v_currMacroScope_3956_;
v_ref_3936_ = v_ref_3957_;
v___y_3937_ = v_a_3931_;
goto v___jp_3932_;
}
else
{
lean_object* v_quotContext_3983_; lean_object* v_currMacroScope_3984_; lean_object* v_ref_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_quotContext_3983_ = lean_ctor_get(v_a_3930_, 1);
v_currMacroScope_3984_ = lean_ctor_get(v_a_3930_, 2);
v_ref_3985_ = lean_ctor_get(v_a_3930_, 5);
v___x_3986_ = 0;
v___x_3987_ = l_Lean_SourceInfo_fromRef(v_ref_3985_, v___x_3986_);
v___x_3988_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_3989_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_3987_);
v___x_3990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3987_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = l_Lean_Syntax_node2(v___x_3987_, v___x_3988_, v___x_3990_, v_s_3929_);
lean_inc(v_currMacroScope_3984_);
lean_inc(v_quotContext_3983_);
v_msg_3933_ = v___x_3991_;
v_quotContext_3934_ = v_quotContext_3983_;
v_currMacroScope_3935_ = v_currMacroScope_3984_;
v_ref_3936_ = v_ref_3985_;
v___y_3937_ = v_a_3931_;
goto v___jp_3932_;
}
v___jp_3932_:
{
uint8_t v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3938_ = 0;
v___x_3939_ = l_Lean_SourceInfo_fromRef(v_ref_3936_, v___x_3938_);
v___x_3940_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3942_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3943_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3944_ = l_Lean_addMacroScope(v_quotContext_3934_, v___x_3943_, v_currMacroScope_3935_);
v___x_3945_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3939_, 3);
v___x_3946_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3939_);
lean_ctor_set(v___x_3946_, 1, v___x_3942_);
lean_ctor_set(v___x_3946_, 2, v___x_3944_);
lean_ctor_set(v___x_3946_, 3, v___x_3945_);
v___x_3947_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3948_ = l_Lean_Syntax_node1(v___x_3939_, v___x_3947_, v_msg_3933_);
v___x_3949_ = l_Lean_Syntax_node2(v___x_3939_, v___x_3941_, v___x_3946_, v___x_3948_);
v___x_3950_ = l_Lean_Syntax_node1(v___x_3939_, v___x_3940_, v___x_3949_);
v___x_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v___y_3937_);
return v___x_3951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_3992_, v_a_3993_, v_a_3994_);
lean_dec_ref(v_a_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4039_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_4036_);
v___x_4040_ = l_Lean_Syntax_isOfKind(v_x_4036_, v___x_4039_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec(v_x_4036_);
v___x_4041_ = lean_box(1);
v___x_4042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
lean_ctor_set(v___x_4042_, 1, v_a_4038_);
return v___x_4042_;
}
else
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v_a_4046_; lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = l_Lean_Syntax_getArg(v_x_4036_, v___x_4043_);
lean_dec(v_x_4036_);
v___x_4045_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_4044_, v_a_4037_, v_a_4038_);
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
v_a_4047_ = lean_ctor_get(v___x_4045_, 1);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4045_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_inc(v_a_4046_);
lean_dec(v___x_4045_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4046_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4055_, v_a_4056_, v_a_4057_);
lean_dec_ref(v_a_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v___x_4067_; lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4087_; 
v___x_4067_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4060_);
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4087_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4067_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4087_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
uint8_t v_verbose_4072_; 
v_verbose_4072_ = lean_ctor_get_uint8(v_a_4068_, 0);
lean_dec(v_a_4068_);
if (v_verbose_4072_ == 0)
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
lean_dec_ref(v_msg_4059_);
v___x_4073_ = lean_box(0);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v___x_4073_);
v___x_4075_ = v___x_4070_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
else
{
lean_object* v_options_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v_options_4077_ = lean_ctor_get(v_a_4064_, 2);
v___x_4078_ = l_Lean_KVMap_instValueBool;
v___x_4079_ = l_Lean_Meta_Sym_sym_debug;
v___x_4080_ = l_Lean_Option_get___redArg(v___x_4078_, v_options_4077_, v___x_4079_);
v___x_4081_ = lean_unbox(v___x_4080_);
lean_dec(v___x_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v___x_4084_; 
lean_dec_ref(v_msg_4059_);
v___x_4082_ = lean_box(0);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v___x_4082_);
v___x_4084_ = v___x_4070_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
else
{
lean_object* v___x_4086_; 
lean_del_object(v___x_4070_);
v___x_4086_ = l_Lean_Meta_Sym_reportIssue(v_msg_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
return v_res_4096_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4099_ = l_String_toRawSubstring_x27(v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_msg_4119_; lean_object* v_quotContext_4120_; lean_object* v_currMacroScope_4121_; lean_object* v_ref_4122_; lean_object* v___y_4123_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
lean_inc(v_s_4115_);
v___x_4138_ = l_Lean_Syntax_getKind(v_s_4115_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4140_ = lean_name_eq(v___x_4138_, v___x_4139_);
lean_dec(v___x_4138_);
if (v___x_4140_ == 0)
{
lean_object* v_quotContext_4141_; lean_object* v_currMacroScope_4142_; lean_object* v_ref_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_quotContext_4141_ = lean_ctor_get(v_a_4116_, 1);
v_currMacroScope_4142_ = lean_ctor_get(v_a_4116_, 2);
v_ref_4143_ = lean_ctor_get(v_a_4116_, 5);
v___x_4144_ = l_Lean_SourceInfo_fromRef(v_ref_4143_, v___x_4140_);
v___x_4145_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4146_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4147_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4144_, 8);
v___x_4148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4144_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4150_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4151_ = lean_box(0);
lean_inc_n(v_currMacroScope_4142_, 3);
lean_inc_n(v_quotContext_4141_, 3);
v___x_4152_ = l_Lean_addMacroScope(v_quotContext_4141_, v___x_4151_, v_currMacroScope_4142_);
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4154_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4144_);
lean_ctor_set(v___x_4154_, 1, v___x_4150_);
lean_ctor_set(v___x_4154_, 2, v___x_4152_);
lean_ctor_set(v___x_4154_, 3, v___x_4153_);
v___x_4155_ = l_Lean_Syntax_node1(v___x_4144_, v___x_4149_, v___x_4154_);
v___x_4156_ = l_Lean_Syntax_node2(v___x_4144_, v___x_4146_, v___x_4148_, v___x_4155_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4144_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4160_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4161_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4162_ = l_Lean_addMacroScope(v_quotContext_4141_, v___x_4161_, v_currMacroScope_4142_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4144_);
lean_ctor_set(v___x_4164_, 1, v___x_4160_);
lean_ctor_set(v___x_4164_, 2, v___x_4162_);
lean_ctor_set(v___x_4164_, 3, v___x_4163_);
v___x_4165_ = l_Lean_Syntax_node1(v___x_4144_, v___x_4159_, v___x_4164_);
v___x_4166_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4144_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Lean_Syntax_node5(v___x_4144_, v___x_4145_, v___x_4156_, v_s_4115_, v___x_4158_, v___x_4165_, v___x_4167_);
v_msg_4119_ = v___x_4168_;
v_quotContext_4120_ = v_quotContext_4141_;
v_currMacroScope_4121_ = v_currMacroScope_4142_;
v_ref_4122_ = v_ref_4143_;
v___y_4123_ = v_a_4117_;
goto v___jp_4118_;
}
else
{
lean_object* v_quotContext_4169_; lean_object* v_currMacroScope_4170_; lean_object* v_ref_4171_; uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_quotContext_4169_ = lean_ctor_get(v_a_4116_, 1);
v_currMacroScope_4170_ = lean_ctor_get(v_a_4116_, 2);
v_ref_4171_ = lean_ctor_get(v_a_4116_, 5);
v___x_4172_ = 0;
v___x_4173_ = l_Lean_SourceInfo_fromRef(v_ref_4171_, v___x_4172_);
v___x_4174_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4175_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4173_);
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4173_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = l_Lean_Syntax_node2(v___x_4173_, v___x_4174_, v___x_4176_, v_s_4115_);
lean_inc(v_currMacroScope_4170_);
lean_inc(v_quotContext_4169_);
v_msg_4119_ = v___x_4177_;
v_quotContext_4120_ = v_quotContext_4169_;
v_currMacroScope_4121_ = v_currMacroScope_4170_;
v_ref_4122_ = v_ref_4171_;
v___y_4123_ = v_a_4117_;
goto v___jp_4118_;
}
v___jp_4118_:
{
uint8_t v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4124_ = 0;
v___x_4125_ = l_Lean_SourceInfo_fromRef(v_ref_4122_, v___x_4124_);
v___x_4126_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4127_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4128_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4129_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4130_ = l_Lean_addMacroScope(v_quotContext_4120_, v___x_4129_, v_currMacroScope_4121_);
v___x_4131_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4125_, 3);
v___x_4132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4125_);
lean_ctor_set(v___x_4132_, 1, v___x_4128_);
lean_ctor_set(v___x_4132_, 2, v___x_4130_);
lean_ctor_set(v___x_4132_, 3, v___x_4131_);
v___x_4133_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4134_ = l_Lean_Syntax_node1(v___x_4125_, v___x_4133_, v_msg_4119_);
v___x_4135_ = l_Lean_Syntax_node2(v___x_4125_, v___x_4127_, v___x_4132_, v___x_4134_);
v___x_4136_ = l_Lean_Syntax_node1(v___x_4125_, v___x_4126_, v___x_4135_);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
lean_ctor_set(v___x_4137_, 1, v___y_4123_);
return v___x_4137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4178_, v_a_4179_, v_a_4180_);
lean_dec_ref(v_a_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4203_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4200_);
v___x_4204_ = l_Lean_Syntax_isOfKind(v_x_4200_, v___x_4203_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec(v_x_4200_);
v___x_4205_ = lean_box(1);
v___x_4206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
lean_ctor_set(v___x_4206_, 1, v_a_4202_);
return v___x_4206_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v_a_4210_; lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v___x_4207_ = lean_unsigned_to_nat(1u);
v___x_4208_ = l_Lean_Syntax_getArg(v_x_4200_, v___x_4207_);
lean_dec(v_x_4200_);
v___x_4209_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4208_, v_a_4201_, v_a_4202_);
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_a_4211_ = lean_ctor_get(v___x_4209_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4209_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4210_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4219_, v_a_4220_, v_a_4221_);
lean_dec_ref(v_a_4220_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4223_){
_start:
{
lean_object* v___x_4225_; lean_object* v_issues_4226_; lean_object* v___x_4227_; 
v___x_4225_ = lean_st_ref_get(v_a_4223_);
v_issues_4226_ = lean_ctor_get(v___x_4225_, 8);
lean_inc(v_issues_4226_);
lean_dec(v___x_4225_);
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_issues_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4228_);
lean_dec(v_a_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4232_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_Meta_Sym_getIssues(v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4247_, lean_object* v_issues_4248_, lean_object* v_a_x3f_4249_){
_start:
{
lean_object* v___x_4251_; lean_object* v_share_4252_; lean_object* v_maxFVar_4253_; lean_object* v_proofInstInfo_4254_; lean_object* v_inferType_4255_; lean_object* v_getLevel_4256_; lean_object* v_congrInfo_4257_; lean_object* v_defEqI_4258_; lean_object* v_extensions_4259_; lean_object* v_issues_4260_; lean_object* v_canon_4261_; lean_object* v_instanceOverrides_4262_; uint8_t v_debug_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4274_; 
v___x_4251_ = lean_st_ref_take(v_a_4247_);
v_share_4252_ = lean_ctor_get(v___x_4251_, 0);
v_maxFVar_4253_ = lean_ctor_get(v___x_4251_, 1);
v_proofInstInfo_4254_ = lean_ctor_get(v___x_4251_, 2);
v_inferType_4255_ = lean_ctor_get(v___x_4251_, 3);
v_getLevel_4256_ = lean_ctor_get(v___x_4251_, 4);
v_congrInfo_4257_ = lean_ctor_get(v___x_4251_, 5);
v_defEqI_4258_ = lean_ctor_get(v___x_4251_, 6);
v_extensions_4259_ = lean_ctor_get(v___x_4251_, 7);
v_issues_4260_ = lean_ctor_get(v___x_4251_, 8);
v_canon_4261_ = lean_ctor_get(v___x_4251_, 9);
v_instanceOverrides_4262_ = lean_ctor_get(v___x_4251_, 10);
v_debug_4263_ = lean_ctor_get_uint8(v___x_4251_, sizeof(void*)*11);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4265_ = v___x_4251_;
v_isShared_4266_ = v_isSharedCheck_4274_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_instanceOverrides_4262_);
lean_inc(v_canon_4261_);
lean_inc(v_issues_4260_);
lean_inc(v_extensions_4259_);
lean_inc(v_defEqI_4258_);
lean_inc(v_congrInfo_4257_);
lean_inc(v_getLevel_4256_);
lean_inc(v_inferType_4255_);
lean_inc(v_proofInstInfo_4254_);
lean_inc(v_maxFVar_4253_);
lean_inc(v_share_4252_);
lean_dec(v___x_4251_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4274_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4267_ = l_List_appendTR___redArg(v_issues_4260_, v_issues_4248_);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 8, v___x_4267_);
v___x_4269_ = v___x_4265_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_share_4252_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_maxFVar_4253_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_proofInstInfo_4254_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v_inferType_4255_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v_getLevel_4256_);
lean_ctor_set(v_reuseFailAlloc_4273_, 5, v_congrInfo_4257_);
lean_ctor_set(v_reuseFailAlloc_4273_, 6, v_defEqI_4258_);
lean_ctor_set(v_reuseFailAlloc_4273_, 7, v_extensions_4259_);
lean_ctor_set(v_reuseFailAlloc_4273_, 8, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4273_, 9, v_canon_4261_);
lean_ctor_set(v_reuseFailAlloc_4273_, 10, v_instanceOverrides_4262_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*11, v_debug_4263_);
v___x_4269_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = lean_st_ref_put(v_a_4247_, v___x_4269_);
v___x_4271_ = lean_box(0);
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4271_);
return v___x_4272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4275_, lean_object* v_issues_4276_, lean_object* v_a_x3f_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4275_, v_issues_4276_, v_a_x3f_4277_);
lean_dec(v_a_x3f_4277_);
lean_dec(v_a_4275_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v_share_4290_; lean_object* v_maxFVar_4291_; lean_object* v_proofInstInfo_4292_; lean_object* v_inferType_4293_; lean_object* v_getLevel_4294_; lean_object* v_congrInfo_4295_; lean_object* v_defEqI_4296_; lean_object* v_extensions_4297_; lean_object* v_canon_4298_; lean_object* v_instanceOverrides_4299_; uint8_t v_debug_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4339_; 
v___x_4288_ = lean_st_ref_get(v_a_4282_);
v___x_4289_ = lean_st_ref_take(v_a_4282_);
v_share_4290_ = lean_ctor_get(v___x_4289_, 0);
v_maxFVar_4291_ = lean_ctor_get(v___x_4289_, 1);
v_proofInstInfo_4292_ = lean_ctor_get(v___x_4289_, 2);
v_inferType_4293_ = lean_ctor_get(v___x_4289_, 3);
v_getLevel_4294_ = lean_ctor_get(v___x_4289_, 4);
v_congrInfo_4295_ = lean_ctor_get(v___x_4289_, 5);
v_defEqI_4296_ = lean_ctor_get(v___x_4289_, 6);
v_extensions_4297_ = lean_ctor_get(v___x_4289_, 7);
v_canon_4298_ = lean_ctor_get(v___x_4289_, 9);
v_instanceOverrides_4299_ = lean_ctor_get(v___x_4289_, 10);
v_debug_4300_ = lean_ctor_get_uint8(v___x_4289_, sizeof(void*)*11);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4339_ == 0)
{
lean_object* v_unused_4340_; 
v_unused_4340_ = lean_ctor_get(v___x_4289_, 8);
lean_dec(v_unused_4340_);
v___x_4302_ = v___x_4289_;
v_isShared_4303_ = v_isSharedCheck_4339_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_instanceOverrides_4299_);
lean_inc(v_canon_4298_);
lean_inc(v_extensions_4297_);
lean_inc(v_defEqI_4296_);
lean_inc(v_congrInfo_4295_);
lean_inc(v_getLevel_4294_);
lean_inc(v_inferType_4293_);
lean_inc(v_proofInstInfo_4292_);
lean_inc(v_maxFVar_4291_);
lean_inc(v_share_4290_);
lean_dec(v___x_4289_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4339_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4304_ = lean_box(0);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 8, v___x_4304_);
v___x_4306_ = v___x_4302_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_share_4290_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_maxFVar_4291_);
lean_ctor_set(v_reuseFailAlloc_4338_, 2, v_proofInstInfo_4292_);
lean_ctor_set(v_reuseFailAlloc_4338_, 3, v_inferType_4293_);
lean_ctor_set(v_reuseFailAlloc_4338_, 4, v_getLevel_4294_);
lean_ctor_set(v_reuseFailAlloc_4338_, 5, v_congrInfo_4295_);
lean_ctor_set(v_reuseFailAlloc_4338_, 6, v_defEqI_4296_);
lean_ctor_set(v_reuseFailAlloc_4338_, 7, v_extensions_4297_);
lean_ctor_set(v_reuseFailAlloc_4338_, 8, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4338_, 9, v_canon_4298_);
lean_ctor_set(v_reuseFailAlloc_4338_, 10, v_instanceOverrides_4299_);
lean_ctor_set_uint8(v_reuseFailAlloc_4338_, sizeof(void*)*11, v_debug_4300_);
v___x_4306_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4307_; lean_object* v_issues_4308_; lean_object* v_r_4309_; 
v___x_4307_ = lean_st_ref_put(v_a_4282_, v___x_4306_);
v_issues_4308_ = lean_ctor_get(v___x_4288_, 8);
lean_inc(v_issues_4308_);
lean_dec(v___x_4288_);
lean_inc(v_a_4286_);
lean_inc_ref(v_a_4285_);
lean_inc(v_a_4284_);
lean_inc_ref(v_a_4283_);
lean_inc(v_a_4282_);
lean_inc_ref(v_a_4281_);
v_r_4309_ = lean_apply_7(v_x_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, lean_box(0));
if (lean_obj_tag(v_r_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4326_; 
v_a_4310_ = lean_ctor_get(v_r_4309_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_r_4309_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4312_ = v_r_4309_;
v_isShared_4313_ = v_isSharedCheck_4326_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v_r_4309_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4326_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
lean_inc(v_a_4310_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 1);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
v___x_4316_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4282_, v_issues_4308_, v___x_4315_);
lean_dec_ref(v___x_4315_);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v___x_4316_, 0);
lean_dec(v_unused_4324_);
v___x_4318_ = v___x_4316_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_dec(v___x_4316_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v_a_4310_);
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4310_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
v_a_4327_ = lean_ctor_get(v_r_4309_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v_r_4309_, 1);
v___x_4328_ = lean_box(0);
v___x_4329_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4282_, v_issues_4308_, v___x_4328_);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4336_ == 0)
{
lean_object* v_unused_4337_; 
v_unused_4337_ = lean_ctor_get(v___x_4329_, 0);
lean_dec(v_unused_4337_);
v___x_4331_ = v___x_4329_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_dec(v___x_4329_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
lean_ctor_set_tag(v___x_4331_, 1);
lean_ctor_set(v___x_4331_, 0, v_a_4327_);
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4327_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4350_, lean_object* v_x_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4360_, lean_object* v_x_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4360_, v_x_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4370_, lean_object* v_vals_4371_, lean_object* v_i_4372_, lean_object* v_k_4373_){
_start:
{
uint8_t v___y_4375_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4381_ = lean_array_get_size(v_keys_4370_);
v___x_4382_ = lean_nat_dec_lt(v_i_4372_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; 
lean_dec(v_i_4372_);
v___x_4383_ = lean_box(0);
return v___x_4383_;
}
else
{
lean_object* v_fst_4384_; lean_object* v_snd_4385_; lean_object* v_k_x27_4386_; lean_object* v_fst_4387_; lean_object* v_snd_4388_; size_t v___x_4389_; size_t v___x_4390_; uint8_t v___x_4391_; 
v_fst_4384_ = lean_ctor_get(v_k_4373_, 0);
v_snd_4385_ = lean_ctor_get(v_k_4373_, 1);
v_k_x27_4386_ = lean_array_fget_borrowed(v_keys_4370_, v_i_4372_);
v_fst_4387_ = lean_ctor_get(v_k_x27_4386_, 0);
v_snd_4388_ = lean_ctor_get(v_k_x27_4386_, 1);
v___x_4389_ = lean_ptr_addr(v_fst_4384_);
v___x_4390_ = lean_ptr_addr(v_fst_4387_);
v___x_4391_ = lean_usize_dec_eq(v___x_4389_, v___x_4390_);
if (v___x_4391_ == 0)
{
v___y_4375_ = v___x_4391_;
goto v___jp_4374_;
}
else
{
size_t v___x_4392_; size_t v___x_4393_; uint8_t v___x_4394_; 
v___x_4392_ = lean_ptr_addr(v_snd_4385_);
v___x_4393_ = lean_ptr_addr(v_snd_4388_);
v___x_4394_ = lean_usize_dec_eq(v___x_4392_, v___x_4393_);
v___y_4375_ = v___x_4394_;
goto v___jp_4374_;
}
}
v___jp_4374_:
{
if (v___y_4375_ == 0)
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_unsigned_to_nat(1u);
v___x_4377_ = lean_nat_add(v_i_4372_, v___x_4376_);
lean_dec(v_i_4372_);
v_i_4372_ = v___x_4377_;
goto _start;
}
else
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = lean_array_fget_borrowed(v_vals_4371_, v_i_4372_);
lean_dec(v_i_4372_);
lean_inc(v___x_4379_);
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
return v___x_4380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4395_, lean_object* v_vals_4396_, lean_object* v_i_4397_, lean_object* v_k_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4395_, v_vals_4396_, v_i_4397_, v_k_4398_);
lean_dec_ref(v_k_4398_);
lean_dec_ref(v_vals_4396_);
lean_dec_ref(v_keys_4395_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4400_, size_t v_x_4401_, lean_object* v_x_4402_){
_start:
{
if (lean_obj_tag(v_x_4400_) == 0)
{
lean_object* v_es_4403_; lean_object* v___x_4404_; size_t v___x_4405_; size_t v___x_4406_; lean_object* v_j_4407_; lean_object* v___x_4408_; 
v_es_4403_ = lean_ctor_get(v_x_4400_, 0);
v___x_4404_ = lean_box(2);
v___x_4405_ = ((size_t)31ULL);
v___x_4406_ = lean_usize_land(v_x_4401_, v___x_4405_);
v_j_4407_ = lean_usize_to_nat(v___x_4406_);
v___x_4408_ = lean_array_get_borrowed(v___x_4404_, v_es_4403_, v_j_4407_);
lean_dec(v_j_4407_);
switch(lean_obj_tag(v___x_4408_))
{
case 0:
{
lean_object* v_key_4409_; lean_object* v_val_4410_; uint8_t v___y_4412_; lean_object* v_fst_4415_; lean_object* v_snd_4416_; lean_object* v_fst_4417_; lean_object* v_snd_4418_; size_t v___x_4419_; size_t v___x_4420_; uint8_t v___x_4421_; 
v_key_4409_ = lean_ctor_get(v___x_4408_, 0);
v_val_4410_ = lean_ctor_get(v___x_4408_, 1);
v_fst_4415_ = lean_ctor_get(v_x_4402_, 0);
v_snd_4416_ = lean_ctor_get(v_x_4402_, 1);
v_fst_4417_ = lean_ctor_get(v_key_4409_, 0);
v_snd_4418_ = lean_ctor_get(v_key_4409_, 1);
v___x_4419_ = lean_ptr_addr(v_fst_4415_);
v___x_4420_ = lean_ptr_addr(v_fst_4417_);
v___x_4421_ = lean_usize_dec_eq(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
v___y_4412_ = v___x_4421_;
goto v___jp_4411_;
}
else
{
size_t v___x_4422_; size_t v___x_4423_; uint8_t v___x_4424_; 
v___x_4422_ = lean_ptr_addr(v_snd_4416_);
v___x_4423_ = lean_ptr_addr(v_snd_4418_);
v___x_4424_ = lean_usize_dec_eq(v___x_4422_, v___x_4423_);
v___y_4412_ = v___x_4424_;
goto v___jp_4411_;
}
v___jp_4411_:
{
if (v___y_4412_ == 0)
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_box(0);
return v___x_4413_;
}
else
{
lean_object* v___x_4414_; 
lean_inc(v_val_4410_);
v___x_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4414_, 0, v_val_4410_);
return v___x_4414_;
}
}
}
case 1:
{
lean_object* v_node_4425_; size_t v___x_4426_; size_t v___x_4427_; 
v_node_4425_ = lean_ctor_get(v___x_4408_, 0);
v___x_4426_ = ((size_t)5ULL);
v___x_4427_ = lean_usize_shift_right(v_x_4401_, v___x_4426_);
v_x_4400_ = v_node_4425_;
v_x_4401_ = v___x_4427_;
goto _start;
}
default: 
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_box(0);
return v___x_4429_;
}
}
}
else
{
lean_object* v_ks_4430_; lean_object* v_vs_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_ks_4430_ = lean_ctor_get(v_x_4400_, 0);
v_vs_4431_ = lean_ctor_get(v_x_4400_, 1);
v___x_4432_ = lean_unsigned_to_nat(0u);
v___x_4433_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4430_, v_vs_4431_, v___x_4432_, v_x_4402_);
return v___x_4433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4434_, lean_object* v_x_4435_, lean_object* v_x_4436_){
_start:
{
size_t v_x_2767__boxed_4437_; lean_object* v_res_4438_; 
v_x_2767__boxed_4437_ = lean_unbox_usize(v_x_4435_);
lean_dec(v_x_4435_);
v_res_4438_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4434_, v_x_2767__boxed_4437_, v_x_4436_);
lean_dec_ref(v_x_4436_);
lean_dec_ref(v_x_4434_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4439_, lean_object* v_x_4440_){
_start:
{
lean_object* v_fst_4441_; lean_object* v_snd_4442_; size_t v___x_4443_; size_t v___x_4444_; size_t v___x_4445_; uint64_t v___x_4446_; size_t v___x_4447_; size_t v___x_4448_; uint64_t v___x_4449_; uint64_t v___x_4450_; size_t v___x_4451_; lean_object* v___x_4452_; 
v_fst_4441_ = lean_ctor_get(v_x_4440_, 0);
v_snd_4442_ = lean_ctor_get(v_x_4440_, 1);
v___x_4443_ = lean_ptr_addr(v_fst_4441_);
v___x_4444_ = ((size_t)3ULL);
v___x_4445_ = lean_usize_shift_right(v___x_4443_, v___x_4444_);
v___x_4446_ = lean_usize_to_uint64(v___x_4445_);
v___x_4447_ = lean_ptr_addr(v_snd_4442_);
v___x_4448_ = lean_usize_shift_right(v___x_4447_, v___x_4444_);
v___x_4449_ = lean_usize_to_uint64(v___x_4448_);
v___x_4450_ = lean_uint64_mix_hash(v___x_4446_, v___x_4449_);
v___x_4451_ = lean_uint64_to_usize(v___x_4450_);
v___x_4452_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4439_, v___x_4451_, v_x_4440_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4453_, lean_object* v_x_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4453_, v_x_4454_);
lean_dec_ref(v_x_4454_);
lean_dec_ref(v_x_4453_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v_x_4458_, lean_object* v_x_4459_){
_start:
{
lean_object* v_ks_4460_; lean_object* v_vs_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4494_; 
v_ks_4460_ = lean_ctor_get(v_x_4456_, 0);
v_vs_4461_ = lean_ctor_get(v_x_4456_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_x_4456_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4463_ = v_x_4456_;
v_isShared_4464_ = v_isSharedCheck_4494_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_vs_4461_);
lean_inc(v_ks_4460_);
lean_dec(v_x_4456_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4494_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
uint8_t v___y_4466_; lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = lean_array_get_size(v_ks_4460_);
v___x_4479_ = lean_nat_dec_lt(v_x_4457_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_del_object(v___x_4463_);
lean_dec(v_x_4457_);
v___x_4480_ = lean_array_push(v_ks_4460_, v_x_4458_);
v___x_4481_ = lean_array_push(v_vs_4461_, v_x_4459_);
v___x_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
return v___x_4482_;
}
else
{
lean_object* v_fst_4483_; lean_object* v_snd_4484_; lean_object* v_k_x27_4485_; lean_object* v_fst_4486_; lean_object* v_snd_4487_; size_t v___x_4488_; size_t v___x_4489_; uint8_t v___x_4490_; 
v_fst_4483_ = lean_ctor_get(v_x_4458_, 0);
v_snd_4484_ = lean_ctor_get(v_x_4458_, 1);
v_k_x27_4485_ = lean_array_fget_borrowed(v_ks_4460_, v_x_4457_);
v_fst_4486_ = lean_ctor_get(v_k_x27_4485_, 0);
v_snd_4487_ = lean_ctor_get(v_k_x27_4485_, 1);
v___x_4488_ = lean_ptr_addr(v_fst_4483_);
v___x_4489_ = lean_ptr_addr(v_fst_4486_);
v___x_4490_ = lean_usize_dec_eq(v___x_4488_, v___x_4489_);
if (v___x_4490_ == 0)
{
v___y_4466_ = v___x_4490_;
goto v___jp_4465_;
}
else
{
size_t v___x_4491_; size_t v___x_4492_; uint8_t v___x_4493_; 
v___x_4491_ = lean_ptr_addr(v_snd_4484_);
v___x_4492_ = lean_ptr_addr(v_snd_4487_);
v___x_4493_ = lean_usize_dec_eq(v___x_4491_, v___x_4492_);
v___y_4466_ = v___x_4493_;
goto v___jp_4465_;
}
}
v___jp_4465_:
{
if (v___y_4466_ == 0)
{
lean_object* v___x_4468_; 
if (v_isShared_4464_ == 0)
{
v___x_4468_ = v___x_4463_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_ks_4460_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_vs_4461_);
v___x_4468_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_unsigned_to_nat(1u);
v___x_4470_ = lean_nat_add(v_x_4457_, v___x_4469_);
lean_dec(v_x_4457_);
v_x_4456_ = v___x_4468_;
v_x_4457_ = v___x_4470_;
goto _start;
}
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4473_ = lean_array_fset(v_ks_4460_, v_x_4457_, v_x_4458_);
v___x_4474_ = lean_array_fset(v_vs_4461_, v_x_4457_, v_x_4459_);
lean_dec(v_x_4457_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v___x_4474_);
lean_ctor_set(v___x_4463_, 0, v___x_4473_);
v___x_4476_ = v___x_4463_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4495_, lean_object* v_k_4496_, lean_object* v_v_4497_){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4495_, v___x_4498_, v_k_4496_, v_v_4497_);
return v___x_4499_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4501_, size_t v_x_4502_, size_t v_x_4503_, lean_object* v_x_4504_, lean_object* v_x_4505_){
_start:
{
if (lean_obj_tag(v_x_4501_) == 0)
{
lean_object* v_es_4506_; size_t v___x_4507_; size_t v___x_4508_; lean_object* v_j_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v_es_4506_ = lean_ctor_get(v_x_4501_, 0);
v___x_4507_ = ((size_t)31ULL);
v___x_4508_ = lean_usize_land(v_x_4502_, v___x_4507_);
v_j_4509_ = lean_usize_to_nat(v___x_4508_);
v___x_4510_ = lean_array_get_size(v_es_4506_);
v___x_4511_ = lean_nat_dec_lt(v_j_4509_, v___x_4510_);
if (v___x_4511_ == 0)
{
lean_dec(v_j_4509_);
lean_dec(v_x_4505_);
lean_dec_ref(v_x_4504_);
return v_x_4501_;
}
else
{
lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4561_; 
lean_inc_ref(v_es_4506_);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_x_4501_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; 
v_unused_4562_ = lean_ctor_get(v_x_4501_, 0);
lean_dec(v_unused_4562_);
v___x_4513_ = v_x_4501_;
v_isShared_4514_ = v_isSharedCheck_4561_;
goto v_resetjp_4512_;
}
else
{
lean_dec(v_x_4501_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4561_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v_v_4515_; lean_object* v___x_4516_; lean_object* v_xs_x27_4517_; lean_object* v___y_4519_; 
v_v_4515_ = lean_array_fget(v_es_4506_, v_j_4509_);
v___x_4516_ = lean_box(0);
v_xs_x27_4517_ = lean_array_fset(v_es_4506_, v_j_4509_, v___x_4516_);
switch(lean_obj_tag(v_v_4515_))
{
case 0:
{
lean_object* v_key_4524_; lean_object* v_val_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4546_; 
v_key_4524_ = lean_ctor_get(v_v_4515_, 0);
v_val_4525_ = lean_ctor_get(v_v_4515_, 1);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_v_4515_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4527_ = v_v_4515_;
v_isShared_4528_ = v_isSharedCheck_4546_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_val_4525_);
lean_inc(v_key_4524_);
lean_dec(v_v_4515_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4546_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
uint8_t v___y_4530_; lean_object* v_fst_4536_; lean_object* v_snd_4537_; lean_object* v_fst_4538_; lean_object* v_snd_4539_; size_t v___x_4540_; size_t v___x_4541_; uint8_t v___x_4542_; 
v_fst_4536_ = lean_ctor_get(v_x_4504_, 0);
v_snd_4537_ = lean_ctor_get(v_x_4504_, 1);
v_fst_4538_ = lean_ctor_get(v_key_4524_, 0);
v_snd_4539_ = lean_ctor_get(v_key_4524_, 1);
v___x_4540_ = lean_ptr_addr(v_fst_4536_);
v___x_4541_ = lean_ptr_addr(v_fst_4538_);
v___x_4542_ = lean_usize_dec_eq(v___x_4540_, v___x_4541_);
if (v___x_4542_ == 0)
{
v___y_4530_ = v___x_4542_;
goto v___jp_4529_;
}
else
{
size_t v___x_4543_; size_t v___x_4544_; uint8_t v___x_4545_; 
v___x_4543_ = lean_ptr_addr(v_snd_4537_);
v___x_4544_ = lean_ptr_addr(v_snd_4539_);
v___x_4545_ = lean_usize_dec_eq(v___x_4543_, v___x_4544_);
v___y_4530_ = v___x_4545_;
goto v___jp_4529_;
}
v___jp_4529_:
{
if (v___y_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_del_object(v___x_4527_);
v___x_4531_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4524_, v_val_4525_, v_x_4504_, v_x_4505_);
v___x_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
v___y_4519_ = v___x_4532_;
goto v___jp_4518_;
}
else
{
lean_object* v___x_4534_; 
lean_dec(v_val_4525_);
lean_dec(v_key_4524_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v_x_4505_);
lean_ctor_set(v___x_4527_, 0, v_x_4504_);
v___x_4534_ = v___x_4527_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_x_4504_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_x_4505_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
v___y_4519_ = v___x_4534_;
goto v___jp_4518_;
}
}
}
}
}
case 1:
{
lean_object* v_node_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4559_; 
v_node_4547_ = lean_ctor_get(v_v_4515_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_v_4515_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4549_ = v_v_4515_;
v_isShared_4550_ = v_isSharedCheck_4559_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_node_4547_);
lean_dec(v_v_4515_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4559_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
size_t v___x_4551_; size_t v___x_4552_; size_t v___x_4553_; size_t v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4557_; 
v___x_4551_ = ((size_t)5ULL);
v___x_4552_ = lean_usize_shift_right(v_x_4502_, v___x_4551_);
v___x_4553_ = ((size_t)1ULL);
v___x_4554_ = lean_usize_add(v_x_4503_, v___x_4553_);
v___x_4555_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4547_, v___x_4552_, v___x_4554_, v_x_4504_, v_x_4505_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4555_);
v___x_4557_ = v___x_4549_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
v___y_4519_ = v___x_4557_;
goto v___jp_4518_;
}
}
}
default: 
{
lean_object* v___x_4560_; 
v___x_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4560_, 0, v_x_4504_);
lean_ctor_set(v___x_4560_, 1, v_x_4505_);
v___y_4519_ = v___x_4560_;
goto v___jp_4518_;
}
}
v___jp_4518_:
{
lean_object* v___x_4520_; lean_object* v___x_4522_; 
v___x_4520_ = lean_array_fset(v_xs_x27_4517_, v_j_4509_, v___y_4519_);
lean_dec(v_j_4509_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4520_);
v___x_4522_ = v___x_4513_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
}
else
{
lean_object* v_ks_4563_; lean_object* v_vs_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4584_; 
v_ks_4563_ = lean_ctor_get(v_x_4501_, 0);
v_vs_4564_ = lean_ctor_get(v_x_4501_, 1);
v_isSharedCheck_4584_ = !lean_is_exclusive(v_x_4501_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4566_ = v_x_4501_;
v_isShared_4567_ = v_isSharedCheck_4584_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_vs_4564_);
lean_inc(v_ks_4563_);
lean_dec(v_x_4501_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4584_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_ks_4563_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_vs_4564_);
v___x_4569_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v_newNode_4570_; uint8_t v___y_4572_; size_t v___x_4578_; uint8_t v___x_4579_; 
v_newNode_4570_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4569_, v_x_4504_, v_x_4505_);
v___x_4578_ = ((size_t)7ULL);
v___x_4579_ = lean_usize_dec_le(v___x_4578_, v_x_4503_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; 
v___x_4580_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4570_);
v___x_4581_ = lean_unsigned_to_nat(4u);
v___x_4582_ = lean_nat_dec_lt(v___x_4580_, v___x_4581_);
lean_dec(v___x_4580_);
v___y_4572_ = v___x_4582_;
goto v___jp_4571_;
}
else
{
v___y_4572_ = v___x_4579_;
goto v___jp_4571_;
}
v___jp_4571_:
{
if (v___y_4572_ == 0)
{
lean_object* v_ks_4573_; lean_object* v_vs_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v_ks_4573_ = lean_ctor_get(v_newNode_4570_, 0);
lean_inc_ref(v_ks_4573_);
v_vs_4574_ = lean_ctor_get(v_newNode_4570_, 1);
lean_inc_ref(v_vs_4574_);
lean_dec_ref(v_newNode_4570_);
v___x_4575_ = lean_unsigned_to_nat(0u);
v___x_4576_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4577_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4503_, v_ks_4573_, v_vs_4574_, v___x_4575_, v___x_4576_);
lean_dec_ref(v_vs_4574_);
lean_dec_ref(v_ks_4573_);
return v___x_4577_;
}
else
{
return v_newNode_4570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4585_, lean_object* v_keys_4586_, lean_object* v_vals_4587_, lean_object* v_i_4588_, lean_object* v_entries_4589_){
_start:
{
lean_object* v___x_4590_; uint8_t v___x_4591_; 
v___x_4590_ = lean_array_get_size(v_keys_4586_);
v___x_4591_ = lean_nat_dec_lt(v_i_4588_, v___x_4590_);
if (v___x_4591_ == 0)
{
lean_dec(v_i_4588_);
return v_entries_4589_;
}
else
{
lean_object* v_k_4592_; lean_object* v_fst_4593_; lean_object* v_snd_4594_; lean_object* v_v_4595_; size_t v___x_4596_; size_t v___x_4597_; size_t v___x_4598_; uint64_t v___x_4599_; size_t v___x_4600_; size_t v___x_4601_; uint64_t v___x_4602_; uint64_t v___x_4603_; size_t v_h_4604_; size_t v___x_4605_; lean_object* v___x_4606_; size_t v___x_4607_; size_t v___x_4608_; size_t v___x_4609_; size_t v_h_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v_k_4592_ = lean_array_fget_borrowed(v_keys_4586_, v_i_4588_);
v_fst_4593_ = lean_ctor_get(v_k_4592_, 0);
v_snd_4594_ = lean_ctor_get(v_k_4592_, 1);
v_v_4595_ = lean_array_fget_borrowed(v_vals_4587_, v_i_4588_);
v___x_4596_ = lean_ptr_addr(v_fst_4593_);
v___x_4597_ = ((size_t)3ULL);
v___x_4598_ = lean_usize_shift_right(v___x_4596_, v___x_4597_);
v___x_4599_ = lean_usize_to_uint64(v___x_4598_);
v___x_4600_ = lean_ptr_addr(v_snd_4594_);
v___x_4601_ = lean_usize_shift_right(v___x_4600_, v___x_4597_);
v___x_4602_ = lean_usize_to_uint64(v___x_4601_);
v___x_4603_ = lean_uint64_mix_hash(v___x_4599_, v___x_4602_);
v_h_4604_ = lean_uint64_to_usize(v___x_4603_);
v___x_4605_ = ((size_t)5ULL);
v___x_4606_ = lean_unsigned_to_nat(1u);
v___x_4607_ = ((size_t)1ULL);
v___x_4608_ = lean_usize_sub(v_depth_4585_, v___x_4607_);
v___x_4609_ = lean_usize_mul(v___x_4605_, v___x_4608_);
v_h_4610_ = lean_usize_shift_right(v_h_4604_, v___x_4609_);
v___x_4611_ = lean_nat_add(v_i_4588_, v___x_4606_);
lean_dec(v_i_4588_);
lean_inc(v_v_4595_);
lean_inc(v_k_4592_);
v___x_4612_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4589_, v_h_4610_, v_depth_4585_, v_k_4592_, v_v_4595_);
v_i_4588_ = v___x_4611_;
v_entries_4589_ = v___x_4612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4614_, lean_object* v_keys_4615_, lean_object* v_vals_4616_, lean_object* v_i_4617_, lean_object* v_entries_4618_){
_start:
{
size_t v_depth_boxed_4619_; lean_object* v_res_4620_; 
v_depth_boxed_4619_ = lean_unbox_usize(v_depth_4614_);
lean_dec(v_depth_4614_);
v_res_4620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4619_, v_keys_4615_, v_vals_4616_, v_i_4617_, v_entries_4618_);
lean_dec_ref(v_vals_4616_);
lean_dec_ref(v_keys_4615_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4621_, lean_object* v_x_4622_, lean_object* v_x_4623_, lean_object* v_x_4624_, lean_object* v_x_4625_){
_start:
{
size_t v_x_2969__boxed_4626_; size_t v_x_2970__boxed_4627_; lean_object* v_res_4628_; 
v_x_2969__boxed_4626_ = lean_unbox_usize(v_x_4622_);
lean_dec(v_x_4622_);
v_x_2970__boxed_4627_ = lean_unbox_usize(v_x_4623_);
lean_dec(v_x_4623_);
v_res_4628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4621_, v_x_2969__boxed_4626_, v_x_2970__boxed_4627_, v_x_4624_, v_x_4625_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4629_, lean_object* v_x_4630_, lean_object* v_x_4631_){
_start:
{
lean_object* v_fst_4632_; lean_object* v_snd_4633_; size_t v___x_4634_; size_t v___x_4635_; size_t v___x_4636_; uint64_t v___x_4637_; size_t v___x_4638_; size_t v___x_4639_; uint64_t v___x_4640_; uint64_t v___x_4641_; size_t v___x_4642_; size_t v___x_4643_; lean_object* v___x_4644_; 
v_fst_4632_ = lean_ctor_get(v_x_4630_, 0);
v_snd_4633_ = lean_ctor_get(v_x_4630_, 1);
v___x_4634_ = lean_ptr_addr(v_fst_4632_);
v___x_4635_ = ((size_t)3ULL);
v___x_4636_ = lean_usize_shift_right(v___x_4634_, v___x_4635_);
v___x_4637_ = lean_usize_to_uint64(v___x_4636_);
v___x_4638_ = lean_ptr_addr(v_snd_4633_);
v___x_4639_ = lean_usize_shift_right(v___x_4638_, v___x_4635_);
v___x_4640_ = lean_usize_to_uint64(v___x_4639_);
v___x_4641_ = lean_uint64_mix_hash(v___x_4637_, v___x_4640_);
v___x_4642_ = lean_uint64_to_usize(v___x_4641_);
v___x_4643_ = ((size_t)1ULL);
v___x_4644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4629_, v___x_4642_, v___x_4643_, v_x_4630_, v_x_4631_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4645_, lean_object* v_t_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v___x_4653_; lean_object* v_defEqI_4654_; lean_object* v_key_4655_; lean_object* v___x_4656_; 
v___x_4653_ = lean_st_ref_get(v_a_4647_);
v_defEqI_4654_ = lean_ctor_get(v___x_4653_, 6);
lean_inc_ref(v_defEqI_4654_);
lean_dec(v___x_4653_);
lean_inc_ref(v_t_4646_);
lean_inc_ref(v_s_4645_);
v_key_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4655_, 0, v_s_4645_);
lean_ctor_set(v_key_4655_, 1, v_t_4646_);
v___x_4656_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4654_, v_key_4655_);
lean_dec_ref(v_defEqI_4654_);
if (lean_obj_tag(v___x_4656_) == 1)
{
lean_object* v_val_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
lean_dec_ref_known(v_key_4655_, 2);
lean_dec_ref(v_t_4646_);
lean_dec_ref(v_s_4645_);
v_val_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_val_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
lean_ctor_set_tag(v___x_4659_, 0);
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_val_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
else
{
lean_object* v___x_4665_; 
lean_dec(v___x_4656_);
v___x_4665_ = l_Lean_Meta_isDefEqI(v_s_4645_, v_t_4646_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4695_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4695_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4695_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v_share_4671_; lean_object* v_maxFVar_4672_; lean_object* v_proofInstInfo_4673_; lean_object* v_inferType_4674_; lean_object* v_getLevel_4675_; lean_object* v_congrInfo_4676_; lean_object* v_defEqI_4677_; lean_object* v_extensions_4678_; lean_object* v_issues_4679_; lean_object* v_canon_4680_; lean_object* v_instanceOverrides_4681_; uint8_t v_debug_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4694_; 
v___x_4670_ = lean_st_ref_take(v_a_4647_);
v_share_4671_ = lean_ctor_get(v___x_4670_, 0);
v_maxFVar_4672_ = lean_ctor_get(v___x_4670_, 1);
v_proofInstInfo_4673_ = lean_ctor_get(v___x_4670_, 2);
v_inferType_4674_ = lean_ctor_get(v___x_4670_, 3);
v_getLevel_4675_ = lean_ctor_get(v___x_4670_, 4);
v_congrInfo_4676_ = lean_ctor_get(v___x_4670_, 5);
v_defEqI_4677_ = lean_ctor_get(v___x_4670_, 6);
v_extensions_4678_ = lean_ctor_get(v___x_4670_, 7);
v_issues_4679_ = lean_ctor_get(v___x_4670_, 8);
v_canon_4680_ = lean_ctor_get(v___x_4670_, 9);
v_instanceOverrides_4681_ = lean_ctor_get(v___x_4670_, 10);
v_debug_4682_ = lean_ctor_get_uint8(v___x_4670_, sizeof(void*)*11);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4684_ = v___x_4670_;
v_isShared_4685_ = v_isSharedCheck_4694_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_instanceOverrides_4681_);
lean_inc(v_canon_4680_);
lean_inc(v_issues_4679_);
lean_inc(v_extensions_4678_);
lean_inc(v_defEqI_4677_);
lean_inc(v_congrInfo_4676_);
lean_inc(v_getLevel_4675_);
lean_inc(v_inferType_4674_);
lean_inc(v_proofInstInfo_4673_);
lean_inc(v_maxFVar_4672_);
lean_inc(v_share_4671_);
lean_dec(v___x_4670_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4694_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; lean_object* v___x_4688_; 
lean_inc(v_a_4666_);
v___x_4686_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4677_, v_key_4655_, v_a_4666_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 6, v___x_4686_);
v___x_4688_ = v___x_4684_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_share_4671_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_maxFVar_4672_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_proofInstInfo_4673_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v_inferType_4674_);
lean_ctor_set(v_reuseFailAlloc_4693_, 4, v_getLevel_4675_);
lean_ctor_set(v_reuseFailAlloc_4693_, 5, v_congrInfo_4676_);
lean_ctor_set(v_reuseFailAlloc_4693_, 6, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4693_, 7, v_extensions_4678_);
lean_ctor_set(v_reuseFailAlloc_4693_, 8, v_issues_4679_);
lean_ctor_set(v_reuseFailAlloc_4693_, 9, v_canon_4680_);
lean_ctor_set(v_reuseFailAlloc_4693_, 10, v_instanceOverrides_4681_);
lean_ctor_set_uint8(v_reuseFailAlloc_4693_, sizeof(void*)*11, v_debug_4682_);
v___x_4688_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4689_ = lean_st_ref_put(v_a_4647_, v___x_4688_);
if (v_isShared_4669_ == 0)
{
v___x_4691_ = v___x_4668_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4666_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4655_, 2);
return v___x_4665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4696_, lean_object* v_t_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4696_, v_t_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4705_, lean_object* v_t_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_){
_start:
{
lean_object* v___x_4714_; 
v___x_4714_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4705_, v_t_4706_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4715_, lean_object* v_t_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Lean_Meta_Sym_isDefEqI(v_s_4715_, v_t_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
lean_dec(v_a_4718_);
lean_dec_ref(v_a_4717_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4725_, lean_object* v_x_4726_, lean_object* v_x_4727_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4726_, v_x_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4729_, lean_object* v_x_4730_, lean_object* v_x_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4729_, v_x_4730_, v_x_4731_);
lean_dec_ref(v_x_4731_);
lean_dec_ref(v_x_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4733_, lean_object* v_x_4734_, lean_object* v_x_4735_, lean_object* v_x_4736_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4734_, v_x_4735_, v_x_4736_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4738_, lean_object* v_x_4739_, size_t v_x_4740_, lean_object* v_x_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4739_, v_x_4740_, v_x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4743_, lean_object* v_x_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_){
_start:
{
size_t v_x_3271__boxed_4747_; lean_object* v_res_4748_; 
v_x_3271__boxed_4747_ = lean_unbox_usize(v_x_4745_);
lean_dec(v_x_4745_);
v_res_4748_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4743_, v_x_4744_, v_x_3271__boxed_4747_, v_x_4746_);
lean_dec_ref(v_x_4746_);
lean_dec_ref(v_x_4744_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4749_, lean_object* v_x_4750_, size_t v_x_4751_, size_t v_x_4752_, lean_object* v_x_4753_, lean_object* v_x_4754_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4750_, v_x_4751_, v_x_4752_, v_x_4753_, v_x_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4756_, lean_object* v_x_4757_, lean_object* v_x_4758_, lean_object* v_x_4759_, lean_object* v_x_4760_, lean_object* v_x_4761_){
_start:
{
size_t v_x_3282__boxed_4762_; size_t v_x_3283__boxed_4763_; lean_object* v_res_4764_; 
v_x_3282__boxed_4762_ = lean_unbox_usize(v_x_4758_);
lean_dec(v_x_4758_);
v_x_3283__boxed_4763_ = lean_unbox_usize(v_x_4759_);
lean_dec(v_x_4759_);
v_res_4764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4756_, v_x_4757_, v_x_3282__boxed_4762_, v_x_3283__boxed_4763_, v_x_4760_, v_x_4761_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4765_, lean_object* v_keys_4766_, lean_object* v_vals_4767_, lean_object* v_heq_4768_, lean_object* v_i_4769_, lean_object* v_k_4770_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4766_, v_vals_4767_, v_i_4769_, v_k_4770_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4772_, lean_object* v_keys_4773_, lean_object* v_vals_4774_, lean_object* v_heq_4775_, lean_object* v_i_4776_, lean_object* v_k_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4772_, v_keys_4773_, v_vals_4774_, v_heq_4775_, v_i_4776_, v_k_4777_);
lean_dec_ref(v_k_4777_);
lean_dec_ref(v_vals_4774_);
lean_dec_ref(v_keys_4773_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4779_, lean_object* v_n_4780_, lean_object* v_k_4781_, lean_object* v_v_4782_){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4780_, v_k_4781_, v_v_4782_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4784_, size_t v_depth_4785_, lean_object* v_keys_4786_, lean_object* v_vals_4787_, lean_object* v_heq_4788_, lean_object* v_i_4789_, lean_object* v_entries_4790_){
_start:
{
lean_object* v___x_4791_; 
v___x_4791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4785_, v_keys_4786_, v_vals_4787_, v_i_4789_, v_entries_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4792_, lean_object* v_depth_4793_, lean_object* v_keys_4794_, lean_object* v_vals_4795_, lean_object* v_heq_4796_, lean_object* v_i_4797_, lean_object* v_entries_4798_){
_start:
{
size_t v_depth_boxed_4799_; lean_object* v_res_4800_; 
v_depth_boxed_4799_ = lean_unbox_usize(v_depth_4793_);
lean_dec(v_depth_4793_);
v_res_4800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4792_, v_depth_boxed_4799_, v_keys_4794_, v_vals_4795_, v_heq_4796_, v_i_4797_, v_entries_4798_);
lean_dec_ref(v_vals_4795_);
lean_dec_ref(v_keys_4794_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4801_, lean_object* v_x_4802_, lean_object* v_x_4803_, lean_object* v_x_4804_, lean_object* v_x_4805_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4802_, v_x_4803_, v_x_4804_, v_x_4805_);
return v___x_4806_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___f_4808_; 
v___x_4807_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4808_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4808_, 0, v___x_4807_);
return v___f_4808_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___f_4810_; 
v___x_4809_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4810_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4810_, 0, v___x_4809_);
return v___f_4810_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2(void){
_start:
{
lean_object* v___f_4811_; lean_object* v___f_4812_; lean_object* v___x_4813_; 
v___f_4811_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v___f_4812_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_4813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___f_4812_);
lean_ctor_set(v___x_4813_, 1, v___f_4811_);
return v___x_4813_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___f_4815_; 
v___x_4814_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4815_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4815_, 0, v___x_4814_);
return v___f_4815_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___f_4817_; 
v___x_4816_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4817_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4817_, 0, v___x_4816_);
return v___f_4817_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5(void){
_start:
{
lean_object* v___f_4818_; lean_object* v___f_4819_; lean_object* v___x_4820_; 
v___f_4818_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4);
v___f_4819_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3);
v___x_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___f_4819_);
lean_ctor_set(v___x_4820_, 1, v___f_4818_);
return v___x_4820_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___f_4822_; 
v___x_4821_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4822_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4822_, 0, v___x_4821_);
return v___f_4822_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_4823_; lean_object* v___f_4824_; 
v___x_4823_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4824_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4824_, 0, v___x_4823_);
return v___f_4824_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_4825_; lean_object* v___f_4826_; lean_object* v___x_4827_; 
v___f_4825_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_4826_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_4827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4827_, 0, v___f_4826_);
lean_ctor_set(v___x_4827_, 1, v___f_4825_);
return v___x_4827_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___f_4829_; 
v___x_4828_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4829_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4829_, 0, v___x_4828_);
return v___f_4829_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___f_4831_; 
v___x_4830_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4831_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4831_, 0, v___x_4830_);
return v___f_4831_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_4832_; lean_object* v___f_4833_; lean_object* v___x_4834_; 
v___f_4832_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_4833_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___f_4833_);
lean_ctor_set(v___x_4834_, 1, v___f_4832_);
return v___x_4834_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4839_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4840_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4841_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4842_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4841_, v___x_4840_, v___x_4839_);
return v___x_4842_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___f_4844_; lean_object* v___f_4845_; lean_object* v___x_4846_; 
v___x_4843_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_4844_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4845_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4846_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4845_, v___f_4844_, v___x_4843_);
return v___x_4846_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18(void){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4847_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_4848_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4849_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4850_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4849_, v___x_4848_, v___x_4847_);
return v___x_4850_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___f_4852_; lean_object* v___f_4853_; lean_object* v___x_4854_; 
v___x_4851_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18);
v___f_4852_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4853_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4854_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4853_, v___f_4852_, v___x_4851_);
return v___x_4854_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20(void){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___f_4857_; 
v___x_4855_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4856_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4857_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4857_, 0, v___x_4856_);
lean_closure_set(v___f_4857_, 1, v___x_4855_);
return v___f_4857_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21(void){
_start:
{
lean_object* v___f_4858_; lean_object* v___f_4859_; lean_object* v___f_4860_; 
v___f_4858_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4859_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20);
v___f_4860_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4860_, 0, v___f_4859_);
lean_closure_set(v___f_4860_, 1, v___f_4858_);
return v___f_4860_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__22));
v___x_4863_ = l_Lean_stringToMessageData(v___x_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4864_){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v_toApplicative_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4934_; 
v___x_4865_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4866_ = l_StateRefT_x27_instMonad___redArg(v___x_4865_);
v_toApplicative_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4934_ == 0)
{
lean_object* v_unused_4935_; 
v_unused_4935_ = lean_ctor_get(v___x_4866_, 1);
lean_dec(v_unused_4935_);
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4934_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_toApplicative_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4934_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v_toFunctor_4871_; lean_object* v_toSeq_4872_; lean_object* v_toSeqLeft_4873_; lean_object* v_toSeqRight_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4932_; 
v_toFunctor_4871_ = lean_ctor_get(v_toApplicative_4867_, 0);
v_toSeq_4872_ = lean_ctor_get(v_toApplicative_4867_, 2);
v_toSeqLeft_4873_ = lean_ctor_get(v_toApplicative_4867_, 3);
v_toSeqRight_4874_ = lean_ctor_get(v_toApplicative_4867_, 4);
v_isSharedCheck_4932_ = !lean_is_exclusive(v_toApplicative_4867_);
if (v_isSharedCheck_4932_ == 0)
{
lean_object* v_unused_4933_; 
v_unused_4933_ = lean_ctor_get(v_toApplicative_4867_, 1);
lean_dec(v_unused_4933_);
v___x_4876_ = v_toApplicative_4867_;
v_isShared_4877_ = v_isSharedCheck_4932_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_toSeqRight_4874_);
lean_inc(v_toSeqLeft_4873_);
lean_inc(v_toSeq_4872_);
lean_inc(v_toFunctor_4871_);
lean_dec(v_toApplicative_4867_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4932_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___f_4878_; lean_object* v___f_4879_; lean_object* v___f_4880_; lean_object* v___f_4881_; lean_object* v___x_4882_; lean_object* v___f_4883_; lean_object* v___f_4884_; lean_object* v___f_4885_; lean_object* v___x_4887_; 
v___f_4878_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4879_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4871_);
v___f_4880_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4880_, 0, v_toFunctor_4871_);
v___f_4881_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4881_, 0, v_toFunctor_4871_);
v___x_4882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___f_4880_);
lean_ctor_set(v___x_4882_, 1, v___f_4881_);
v___f_4883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4883_, 0, v_toSeqRight_4874_);
v___f_4884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4884_, 0, v_toSeqLeft_4873_);
v___f_4885_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4885_, 0, v_toSeq_4872_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 4, v___f_4883_);
lean_ctor_set(v___x_4876_, 3, v___f_4884_);
lean_ctor_set(v___x_4876_, 2, v___f_4885_);
lean_ctor_set(v___x_4876_, 1, v___f_4878_);
lean_ctor_set(v___x_4876_, 0, v___x_4882_);
v___x_4887_ = v___x_4876_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v___f_4878_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v___f_4885_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v___f_4884_);
lean_ctor_set(v_reuseFailAlloc_4931_, 4, v___f_4883_);
v___x_4887_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4889_; 
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 1, v___f_4879_);
lean_ctor_set(v___x_4869_, 0, v___x_4887_);
v___x_4889_ = v___x_4869_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4887_);
lean_ctor_set(v_reuseFailAlloc_4930_, 1, v___f_4879_);
v___x_4889_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
lean_object* v___x_4890_; lean_object* v_toApplicative_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4928_; 
v___x_4890_ = l_StateRefT_x27_instMonad___redArg(v___x_4889_);
v_toApplicative_4891_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4928_ == 0)
{
lean_object* v_unused_4929_; 
v_unused_4929_ = lean_ctor_get(v___x_4890_, 1);
lean_dec(v_unused_4929_);
v___x_4893_ = v___x_4890_;
v_isShared_4894_ = v_isSharedCheck_4928_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_toApplicative_4891_);
lean_dec(v___x_4890_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4928_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v_toFunctor_4895_; lean_object* v_toSeq_4896_; lean_object* v_toSeqLeft_4897_; lean_object* v_toSeqRight_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4926_; 
v_toFunctor_4895_ = lean_ctor_get(v_toApplicative_4891_, 0);
v_toSeq_4896_ = lean_ctor_get(v_toApplicative_4891_, 2);
v_toSeqLeft_4897_ = lean_ctor_get(v_toApplicative_4891_, 3);
v_toSeqRight_4898_ = lean_ctor_get(v_toApplicative_4891_, 4);
v_isSharedCheck_4926_ = !lean_is_exclusive(v_toApplicative_4891_);
if (v_isSharedCheck_4926_ == 0)
{
lean_object* v_unused_4927_; 
v_unused_4927_ = lean_ctor_get(v_toApplicative_4891_, 1);
lean_dec(v_unused_4927_);
v___x_4900_ = v_toApplicative_4891_;
v_isShared_4901_ = v_isSharedCheck_4926_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_toSeqRight_4898_);
lean_inc(v_toSeqLeft_4897_);
lean_inc(v_toSeq_4896_);
lean_inc(v_toFunctor_4895_);
lean_dec(v_toApplicative_4891_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4926_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___f_4902_; lean_object* v___f_4903_; lean_object* v___f_4904_; lean_object* v___f_4905_; lean_object* v___x_4906_; lean_object* v___f_4907_; lean_object* v___f_4908_; lean_object* v___f_4909_; lean_object* v___x_4911_; 
v___f_4902_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4903_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4895_);
v___f_4904_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4904_, 0, v_toFunctor_4895_);
v___f_4905_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4905_, 0, v_toFunctor_4895_);
v___x_4906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___f_4904_);
lean_ctor_set(v___x_4906_, 1, v___f_4905_);
v___f_4907_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4907_, 0, v_toSeqRight_4898_);
v___f_4908_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4908_, 0, v_toSeqLeft_4897_);
v___f_4909_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4909_, 0, v_toSeq_4896_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 4, v___f_4907_);
lean_ctor_set(v___x_4900_, 3, v___f_4908_);
lean_ctor_set(v___x_4900_, 2, v___f_4909_);
lean_ctor_set(v___x_4900_, 1, v___f_4902_);
lean_ctor_set(v___x_4900_, 0, v___x_4906_);
v___x_4911_ = v___x_4900_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4906_);
lean_ctor_set(v_reuseFailAlloc_4925_, 1, v___f_4902_);
lean_ctor_set(v_reuseFailAlloc_4925_, 2, v___f_4909_);
lean_ctor_set(v_reuseFailAlloc_4925_, 3, v___f_4908_);
lean_ctor_set(v_reuseFailAlloc_4925_, 4, v___f_4907_);
v___x_4911_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
lean_object* v___x_4913_; 
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 1, v___f_4903_);
lean_ctor_set(v___x_4893_, 0, v___x_4911_);
v___x_4913_ = v___x_4893_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4911_);
lean_ctor_set(v_reuseFailAlloc_4924_, 1, v___f_4903_);
v___x_4913_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v_toMonadRef_4918_; lean_object* v___f_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4914_ = l_StateRefT_x27_instMonad___redArg(v___x_4913_);
v___x_4915_ = l_ReaderT_instMonad___redArg(v___x_4914_);
v___x_4916_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___x_4917_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19);
v_toMonadRef_4918_ = lean_ctor_get(v___x_4917_, 0);
v___f_4919_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21);
lean_inc_ref(v___x_4915_);
v___x_4920_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4919_, v___x_4915_);
lean_inc_ref(v_toMonadRef_4918_);
v___x_4921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4916_);
lean_ctor_set(v___x_4921_, 1, v_toMonadRef_4918_);
lean_ctor_set(v___x_4921_, 2, v___x_4920_);
v___x_4922_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_4923_ = l_Lean_throwError___redArg(v___x_4915_, v___x_4921_, v___x_4922_);
return v___x_4923_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4936_, lean_object* v_extensions_4937_){
_start:
{
lean_object* v_id_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v_id_4939_ = lean_ctor_get(v_ext_4936_, 0);
v___x_4940_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4941_ = lean_array_get_borrowed(v___x_4940_, v_extensions_4937_, v_id_4939_);
lean_inc(v___x_4941_);
v___x_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4941_);
return v___x_4942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4943_, lean_object* v_extensions_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4943_, v_extensions_4944_);
lean_dec_ref(v_extensions_4944_);
lean_dec_ref(v_ext_4943_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_4947_, lean_object* v_ext_4948_, lean_object* v_extensions_4949_){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4948_, v_extensions_4949_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_4952_, lean_object* v_ext_4953_, lean_object* v_extensions_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_4952_, v_ext_4953_, v_extensions_4954_);
lean_dec_ref(v_extensions_4954_);
lean_dec_ref(v_ext_4953_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v___x_4961_; lean_object* v_extensions_4962_; lean_object* v___x_4963_; 
v___x_4961_ = lean_st_ref_get(v_a_4958_);
v_extensions_4962_ = lean_ctor_get(v___x_4961_, 7);
lean_inc_ref(v_extensions_4962_);
lean_dec(v___x_4961_);
v___x_4963_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4957_, v_extensions_4962_);
lean_dec_ref(v_extensions_4962_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4963_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4963_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4984_; 
v_a_4972_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4974_ = v___x_4963_;
v_isShared_4975_ = v_isSharedCheck_4984_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4963_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4984_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v_ref_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4982_; 
v_ref_4976_ = lean_ctor_get(v_a_4959_, 5);
v___x_4977_ = lean_io_error_to_string(v_a_4972_);
v___x_4978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
v___x_4979_ = l_Lean_MessageData_ofFormat(v___x_4978_);
lean_inc(v_ref_4976_);
v___x_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4980_, 0, v_ref_4976_);
lean_ctor_set(v___x_4980_, 1, v___x_4979_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v___x_4980_);
v___x_4982_ = v___x_4974_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v___x_4980_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4985_, v_a_4986_, v_a_4987_);
lean_dec_ref(v_a_4987_);
lean_dec(v_a_4986_);
lean_dec_ref(v_ext_4985_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_4990_, lean_object* v_ext_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4991_, v_a_4993_, v_a_4996_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_5000_, lean_object* v_ext_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_5000_, v_ext_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
lean_dec(v_a_5007_);
lean_dec_ref(v_a_5006_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec_ref(v_ext_5001_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_5010_, lean_object* v_f_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v___x_5014_; lean_object* v_share_5015_; lean_object* v_maxFVar_5016_; lean_object* v_proofInstInfo_5017_; lean_object* v_inferType_5018_; lean_object* v_getLevel_5019_; lean_object* v_congrInfo_5020_; lean_object* v_defEqI_5021_; lean_object* v_extensions_5022_; lean_object* v_issues_5023_; lean_object* v_canon_5024_; lean_object* v_instanceOverrides_5025_; uint8_t v_debug_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5045_; 
v___x_5014_ = lean_st_ref_take(v_a_5012_);
v_share_5015_ = lean_ctor_get(v___x_5014_, 0);
v_maxFVar_5016_ = lean_ctor_get(v___x_5014_, 1);
v_proofInstInfo_5017_ = lean_ctor_get(v___x_5014_, 2);
v_inferType_5018_ = lean_ctor_get(v___x_5014_, 3);
v_getLevel_5019_ = lean_ctor_get(v___x_5014_, 4);
v_congrInfo_5020_ = lean_ctor_get(v___x_5014_, 5);
v_defEqI_5021_ = lean_ctor_get(v___x_5014_, 6);
v_extensions_5022_ = lean_ctor_get(v___x_5014_, 7);
v_issues_5023_ = lean_ctor_get(v___x_5014_, 8);
v_canon_5024_ = lean_ctor_get(v___x_5014_, 9);
v_instanceOverrides_5025_ = lean_ctor_get(v___x_5014_, 10);
v_debug_5026_ = lean_ctor_get_uint8(v___x_5014_, sizeof(void*)*11);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5028_ = v___x_5014_;
v_isShared_5029_ = v_isSharedCheck_5045_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_instanceOverrides_5025_);
lean_inc(v_canon_5024_);
lean_inc(v_issues_5023_);
lean_inc(v_extensions_5022_);
lean_inc(v_defEqI_5021_);
lean_inc(v_congrInfo_5020_);
lean_inc(v_getLevel_5019_);
lean_inc(v_inferType_5018_);
lean_inc(v_proofInstInfo_5017_);
lean_inc(v_maxFVar_5016_);
lean_inc(v_share_5015_);
lean_dec(v___x_5014_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5045_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v_id_5030_; lean_object* v___x_5031_; lean_object* v___y_5033_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v_id_5030_ = lean_ctor_get(v_ext_5010_, 0);
v___x_5031_ = lean_box(0);
v___x_5039_ = lean_array_get_size(v_extensions_5022_);
v___x_5040_ = lean_nat_dec_lt(v_id_5030_, v___x_5039_);
if (v___x_5040_ == 0)
{
lean_dec(v_f_5011_);
v___y_5033_ = v_extensions_5022_;
goto v___jp_5032_;
}
else
{
lean_object* v_v_5041_; lean_object* v_xs_x27_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v_v_5041_ = lean_array_fget(v_extensions_5022_, v_id_5030_);
v_xs_x27_5042_ = lean_array_fset(v_extensions_5022_, v_id_5030_, v___x_5031_);
v___x_5043_ = lean_apply_1(v_f_5011_, v_v_5041_);
v___x_5044_ = lean_array_fset(v_xs_x27_5042_, v_id_5030_, v___x_5043_);
v___y_5033_ = v___x_5044_;
goto v___jp_5032_;
}
v___jp_5032_:
{
lean_object* v___x_5035_; 
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 7, v___y_5033_);
v___x_5035_ = v___x_5028_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_share_5015_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v_maxFVar_5016_);
lean_ctor_set(v_reuseFailAlloc_5038_, 2, v_proofInstInfo_5017_);
lean_ctor_set(v_reuseFailAlloc_5038_, 3, v_inferType_5018_);
lean_ctor_set(v_reuseFailAlloc_5038_, 4, v_getLevel_5019_);
lean_ctor_set(v_reuseFailAlloc_5038_, 5, v_congrInfo_5020_);
lean_ctor_set(v_reuseFailAlloc_5038_, 6, v_defEqI_5021_);
lean_ctor_set(v_reuseFailAlloc_5038_, 7, v___y_5033_);
lean_ctor_set(v_reuseFailAlloc_5038_, 8, v_issues_5023_);
lean_ctor_set(v_reuseFailAlloc_5038_, 9, v_canon_5024_);
lean_ctor_set(v_reuseFailAlloc_5038_, 10, v_instanceOverrides_5025_);
lean_ctor_set_uint8(v_reuseFailAlloc_5038_, sizeof(void*)*11, v_debug_5026_);
v___x_5035_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5036_ = lean_st_ref_put(v_a_5012_, v___x_5035_);
v___x_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5031_);
return v___x_5037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_5046_, lean_object* v_f_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5046_, v_f_5047_, v_a_5048_);
lean_dec(v_a_5048_);
lean_dec_ref(v_ext_5046_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_5051_, lean_object* v_ext_5052_, lean_object* v_f_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5052_, v_f_5053_, v_a_5055_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5062_, lean_object* v_ext_5063_, lean_object* v_f_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5062_, v_ext_5063_, v_f_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
lean_dec(v_a_5070_);
lean_dec_ref(v_a_5069_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec_ref(v_ext_5063_);
return v_res_5072_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_sym_debug = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_sym_debug);
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_instInhabitedSymExtensionState = _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedSymExtensionState);
res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_SymM(builtin);
}
#ifdef __cplusplus
}
#endif
