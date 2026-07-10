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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__11;
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
lean_object* v___x_178_; 
v___x_178_ = l_Lean_initializing();
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_198_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_198_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_198_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_198_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v___x_183_; 
v___x_183_ = lean_unbox(v_a_179_);
lean_dec(v_a_179_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec_ref(v_mkInitial_176_);
v___x_184_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 1);
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_188_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_189_ = lean_st_ref_get(v___x_188_);
v___x_190_ = lean_st_ref_take(v___x_188_);
v___x_191_ = lean_array_get_size(v___x_189_);
lean_dec(v___x_189_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_mkInitial_176_);
lean_inc_ref(v___x_192_);
v___x_193_ = lean_array_push(v___x_190_, v___x_192_);
v___x_194_ = lean_st_ref_set(v___x_188_, v___x_193_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_192_);
v___x_196_ = v___x_181_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_192_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v_mkInitial_176_);
v_a_199_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_178_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_178_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_210_, lean_object* v_mkInitial_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_214_, lean_object* v_mkInitial_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_214_, v_mkInitial_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_218_, size_t v_i_219_, lean_object* v_bs_220_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_lt(v_i_219_, v_sz_218_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_bs_220_);
return v___x_223_;
}
else
{
lean_object* v_v_224_; lean_object* v_mkInitial_225_; lean_object* v___x_226_; 
v_v_224_ = lean_array_uget_borrowed(v_bs_220_, v_i_219_);
v_mkInitial_225_ = lean_ctor_get(v_v_224_, 1);
lean_inc_ref(v_mkInitial_225_);
v___x_226_ = lean_apply_1(v_mkInitial_225_, lean_box(0));
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v_bs_x27_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = lean_unsigned_to_nat(0u);
v_bs_x27_229_ = lean_array_uset(v_bs_220_, v_i_219_, v___x_228_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_219_, v___x_230_);
v___x_232_ = lean_array_uset(v_bs_x27_229_, v_i_219_, v_a_227_);
v_i_219_ = v___x_231_;
v_bs_220_ = v___x_232_;
goto _start;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_bs_220_);
v_a_234_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_226_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_226_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_bs_244_, lean_object* v___y_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_247_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_246_, v_i_boxed_247_, v_bs_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; size_t v_sz_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_250_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_251_ = lean_st_ref_get(v___x_250_);
v_sz_252_ = lean_array_size(v___x_251_);
v___x_253_ = ((size_t)0ULL);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_252_, v___x_253_, v___x_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object* v_x_265_){
_start:
{
switch(lean_obj_tag(v_x_265_))
{
case 0:
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(0u);
return v___x_266_;
}
case 1:
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(1u);
return v___x_267_;
}
case 2:
{
lean_object* v___x_268_; 
v___x_268_ = lean_unsigned_to_nat(2u);
return v___x_268_;
}
default: 
{
lean_object* v___x_269_; 
v___x_269_ = lean_unsigned_to_nat(3u);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object* v_x_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_270_);
lean_dec(v_x_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
switch(lean_obj_tag(v_t_272_))
{
case 0:
{
return v_k_273_;
}
case 1:
{
lean_object* v_prefixSize_274_; lean_object* v_suffixSize_275_; lean_object* v___x_276_; 
v_prefixSize_274_ = lean_ctor_get(v_t_272_, 0);
lean_inc(v_prefixSize_274_);
v_suffixSize_275_ = lean_ctor_get(v_t_272_, 1);
lean_inc(v_suffixSize_275_);
lean_dec_ref_known(v_t_272_, 2);
v___x_276_ = lean_apply_2(v_k_273_, v_prefixSize_274_, v_suffixSize_275_);
return v___x_276_;
}
default: 
{
lean_object* v_rewritable_277_; lean_object* v___x_278_; 
v_rewritable_277_ = lean_ctor_get(v_t_272_, 0);
lean_inc_ref(v_rewritable_277_);
lean_dec(v_t_272_);
v___x_278_ = lean_apply_1(v_k_273_, v_rewritable_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_279_, lean_object* v_ctorIdx_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_k_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_281_, v_k_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_285_, lean_object* v_ctorIdx_286_, lean_object* v_t_287_, lean_object* v_h_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_285_, v_ctorIdx_286_, v_t_287_, v_h_288_, v_k_289_);
lean_dec(v_ctorIdx_286_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_291_, lean_object* v_none_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_291_, v_none_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_none_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_295_, v_none_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_299_, lean_object* v_fixedPrefix_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_299_, v_fixedPrefix_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_fixedPrefix_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_303_, v_fixedPrefix_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_307_, lean_object* v_interlaced_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_307_, v_interlaced_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_interlaced_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_311_, v_interlaced_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_315_, lean_object* v_congrTheorem_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_315_, v_congrTheorem_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_congrTheorem_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_319_, v_congrTheorem_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Expr_getAppFn(v_e_329_);
if (lean_obj_tag(v___x_335_) == 4)
{
lean_object* v_declName_336_; lean_object* v___x_337_; lean_object* v_env_338_; uint8_t v___x_339_; 
v_declName_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_declName_336_);
lean_dec_ref_known(v___x_335_, 2);
v___x_337_ = lean_st_ref_get(v_a_333_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_338_);
lean_dec(v___x_337_);
v___x_339_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_338_, v_declName_336_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_e_329_);
v___x_340_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_342_ = 0;
v___x_343_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_329_, v___x_342_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_363_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_363_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
if (lean_obj_tag(v_a_344_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_358_; 
v_val_348_ = lean_ctor_get(v_a_344_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_a_344_);
if (v_isSharedCheck_358_ == 0)
{
v___x_350_ = v_a_344_;
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v_a_344_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_val_348_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_353_);
v___x_355_ = v___x_346_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_a_344_);
v___x_359_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_359_);
v___x_361_ = v___x_346_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_343_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_343_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v_e_329_);
v___x_372_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_381_, lean_object* v_e_382_){
_start:
{
if (lean_obj_tag(v_e_382_) == 4)
{
lean_object* v_declName_383_; uint8_t v___x_384_; 
v_declName_383_ = lean_ctor_get(v_e_382_, 0);
lean_inc(v_declName_383_);
lean_dec_ref_known(v_e_382_, 2);
v___x_384_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_381_, v_declName_383_);
return v___x_384_;
}
else
{
uint8_t v___x_385_; 
lean_dec_ref(v_e_382_);
lean_dec_ref(v_env_381_);
v___x_385_ = 0;
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_386_, lean_object* v_e_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_386_, v_e_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; lean_object* v_env_394_; lean_object* v___f_395_; lean_object* v___x_396_; 
v___x_393_ = lean_st_ref_get(v_a_391_);
v_env_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_env_394_);
lean_dec(v___x_393_);
v___f_395_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_395_, 0, v_env_394_);
v___x_396_ = lean_find_expr(v___f_395_, v_e_390_);
lean_dec_ref(v___f_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = 0;
v___x_398_ = lean_box(v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
else
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_396_, 0);
lean_dec(v_unused_409_);
v___x_401_ = v___x_396_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_396_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = 1;
v___x_404_ = lean_box(v___x_403_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_e_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_414_, v_a_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec_ref(v_e_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_e_424_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_439_, lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_apply_1(v_x_440_, lean_box(0));
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_448_, lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_448_, v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
else
{
lean_object* v_key_459_; lean_object* v_tail_460_; uint8_t v___x_461_; 
v_key_459_ = lean_ctor_get(v_x_457_, 0);
v_tail_460_ = lean_ctor_get(v_x_457_, 2);
v___x_461_ = l_Lean_ExprStructEq_beq(v_key_459_, v_a_456_);
if (v___x_461_ == 0)
{
v_x_457_ = v_tail_460_;
goto _start;
}
else
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec_ref(v_a_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
return v_x_467_;
}
else
{
lean_object* v_key_469_; lean_object* v_value_470_; lean_object* v_tail_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_494_; 
v_key_469_ = lean_ctor_get(v_x_468_, 0);
v_value_470_ = lean_ctor_get(v_x_468_, 1);
v_tail_471_ = lean_ctor_get(v_x_468_, 2);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_494_ == 0)
{
v___x_473_ = v_x_468_;
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_tail_471_);
lean_inc(v_value_470_);
lean_inc(v_key_469_);
lean_dec(v_x_468_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v_fold_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_475_ = lean_array_get_size(v_x_467_);
v___x_476_ = l_Lean_ExprStructEq_hash(v_key_469_);
v___x_477_ = 32ULL;
v___x_478_ = lean_uint64_shift_right(v___x_476_, v___x_477_);
v_fold_479_ = lean_uint64_xor(v___x_476_, v___x_478_);
v___x_480_ = 16ULL;
v___x_481_ = lean_uint64_shift_right(v_fold_479_, v___x_480_);
v___x_482_ = lean_uint64_xor(v_fold_479_, v___x_481_);
v___x_483_ = lean_uint64_to_usize(v___x_482_);
v___x_484_ = lean_usize_of_nat(v___x_475_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_sub(v___x_484_, v___x_485_);
v___x_487_ = lean_usize_land(v___x_483_, v___x_486_);
v___x_488_ = lean_array_uget_borrowed(v_x_467_, v___x_487_);
lean_inc(v___x_488_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v___x_488_);
v___x_490_ = v___x_473_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_key_469_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_value_470_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v___x_488_);
v___x_490_ = v_reuseFailAlloc_493_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_array_uset(v_x_467_, v___x_487_, v___x_490_);
v_x_467_ = v___x_491_;
v_x_468_ = v_tail_471_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_495_, lean_object* v_source_496_, lean_object* v_target_497_){
_start:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_array_get_size(v_source_496_);
v___x_499_ = lean_nat_dec_lt(v_i_495_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec_ref(v_source_496_);
lean_dec(v_i_495_);
return v_target_497_;
}
else
{
lean_object* v_es_500_; lean_object* v___x_501_; lean_object* v_source_502_; lean_object* v_target_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_es_500_ = lean_array_fget(v_source_496_, v_i_495_);
v___x_501_ = lean_box(0);
v_source_502_ = lean_array_fset(v_source_496_, v_i_495_, v___x_501_);
v_target_503_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_497_, v_es_500_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_i_495_, v___x_504_);
lean_dec(v_i_495_);
v_i_495_ = v___x_505_;
v_source_496_ = v_source_502_;
v_target_497_ = v_target_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_nbuckets_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_508_ = lean_array_get_size(v_data_507_);
v___x_509_ = lean_unsigned_to_nat(2u);
v_nbuckets_510_ = lean_nat_mul(v___x_508_, v___x_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_box(0);
v___x_513_ = lean_mk_array(v_nbuckets_510_, v___x_512_);
v___x_514_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_511_, v_data_507_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_515_, lean_object* v_b_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_dec(v_b_516_);
lean_dec_ref(v_a_515_);
return v_x_517_;
}
else
{
lean_object* v_key_518_; lean_object* v_value_519_; lean_object* v_tail_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_532_; 
v_key_518_ = lean_ctor_get(v_x_517_, 0);
v_value_519_ = lean_ctor_get(v_x_517_, 1);
v_tail_520_ = lean_ctor_get(v_x_517_, 2);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_532_ == 0)
{
v___x_522_ = v_x_517_;
v_isShared_523_ = v_isSharedCheck_532_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_tail_520_);
lean_inc(v_value_519_);
lean_inc(v_key_518_);
lean_dec(v_x_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_532_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_ExprStructEq_beq(v_key_518_, v_a_515_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_515_, v_b_516_, v_tail_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v___x_525_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_key_518_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_value_519_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v_value_519_);
lean_dec(v_key_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v_b_516_);
lean_ctor_set(v___x_522_, 0, v_a_515_);
v___x_530_ = v___x_522_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_515_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_b_516_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_tail_520_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_533_, lean_object* v_a_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_size_536_; lean_object* v_buckets_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_580_; 
v_size_536_ = lean_ctor_get(v_m_533_, 0);
v_buckets_537_ = lean_ctor_get(v_m_533_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_m_533_);
if (v_isSharedCheck_580_ == 0)
{
v___x_539_ = v_m_533_;
v_isShared_540_ = v_isSharedCheck_580_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_buckets_537_);
lean_inc(v_size_536_);
lean_dec(v_m_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_580_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v_fold_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v_bkt_554_; uint8_t v___x_555_; 
v___x_541_ = lean_array_get_size(v_buckets_537_);
v___x_542_ = l_Lean_ExprStructEq_hash(v_a_534_);
v___x_543_ = 32ULL;
v___x_544_ = lean_uint64_shift_right(v___x_542_, v___x_543_);
v_fold_545_ = lean_uint64_xor(v___x_542_, v___x_544_);
v___x_546_ = 16ULL;
v___x_547_ = lean_uint64_shift_right(v_fold_545_, v___x_546_);
v___x_548_ = lean_uint64_xor(v_fold_545_, v___x_547_);
v___x_549_ = lean_uint64_to_usize(v___x_548_);
v___x_550_ = lean_usize_of_nat(v___x_541_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_usize_land(v___x_549_, v___x_552_);
v_bkt_554_ = lean_array_uget_borrowed(v_buckets_537_, v___x_553_);
v___x_555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_534_, v_bkt_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v_size_x27_557_; lean_object* v___x_558_; lean_object* v_buckets_x27_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v_size_x27_557_ = lean_nat_add(v_size_536_, v___x_556_);
lean_dec(v_size_536_);
lean_inc(v_bkt_554_);
v___x_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_558_, 0, v_a_534_);
lean_ctor_set(v___x_558_, 1, v_b_535_);
lean_ctor_set(v___x_558_, 2, v_bkt_554_);
v_buckets_x27_559_ = lean_array_uset(v_buckets_537_, v___x_553_, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(4u);
v___x_561_ = lean_nat_mul(v_size_x27_557_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(3u);
v___x_563_ = lean_nat_div(v___x_561_, v___x_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_array_get_size(v_buckets_x27_559_);
v___x_565_ = lean_nat_dec_le(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
if (v___x_565_ == 0)
{
lean_object* v_val_566_; lean_object* v___x_568_; 
v_val_566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_559_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_val_566_);
lean_ctor_set(v___x_539_, 0, v_size_x27_557_);
v___x_568_ = v___x_539_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_size_x27_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_val_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
lean_object* v___x_571_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_buckets_x27_559_);
lean_ctor_set(v___x_539_, 0, v_size_x27_557_);
v___x_571_ = v___x_539_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_x27_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_buckets_x27_559_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v___x_573_; lean_object* v_buckets_x27_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_bkt_554_);
v___x_573_ = lean_box(0);
v_buckets_x27_574_ = lean_array_uset(v_buckets_537_, v___x_553_, v___x_573_);
v___x_575_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_534_, v_b_535_, v_bkt_554_);
v___x_576_ = lean_array_uset(v_buckets_x27_574_, v___x_553_, v___x_575_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_576_);
v___x_578_ = v___x_539_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_size_536_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_581_, lean_object* v_e_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_st_ref_take(v_a_581_);
v___x_586_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_585_, v_e_582_, v_a_583_);
v___x_587_ = lean_st_ref_set(v_a_581_, v___x_586_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_589_, lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_589_, v_e_590_, v_a_591_);
lean_dec(v_a_589_);
return v_res_593_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Lean_maxRecDepthErrorMessage;
v___x_600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_602_ = l_Lean_MessageData_ofFormat(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_604_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_605_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_606_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_ref_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___y_622_; lean_object* v_fileName_631_; lean_object* v_fileMap_632_; lean_object* v_options_633_; lean_object* v_currRecDepth_634_; lean_object* v_maxRecDepth_635_; lean_object* v_ref_636_; lean_object* v_currNamespace_637_; lean_object* v_openDecls_638_; lean_object* v_initHeartbeats_639_; lean_object* v_maxHeartbeats_640_; lean_object* v_quotContext_641_; lean_object* v_currMacroScope_642_; uint8_t v_diag_643_; lean_object* v_cancelTk_x3f_644_; uint8_t v_suppressElabErrors_645_; lean_object* v_inheritedTraceOptions_646_; uint8_t v___y_648_; lean_object* v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; 
v_fileName_631_ = lean_ctor_get(v___y_618_, 0);
v_fileMap_632_ = lean_ctor_get(v___y_618_, 1);
v_options_633_ = lean_ctor_get(v___y_618_, 2);
v_currRecDepth_634_ = lean_ctor_get(v___y_618_, 3);
v_maxRecDepth_635_ = lean_ctor_get(v___y_618_, 4);
v_ref_636_ = lean_ctor_get(v___y_618_, 5);
v_currNamespace_637_ = lean_ctor_get(v___y_618_, 6);
v_openDecls_638_ = lean_ctor_get(v___y_618_, 7);
v_initHeartbeats_639_ = lean_ctor_get(v___y_618_, 8);
v_maxHeartbeats_640_ = lean_ctor_get(v___y_618_, 9);
v_quotContext_641_ = lean_ctor_get(v___y_618_, 10);
v_currMacroScope_642_ = lean_ctor_get(v___y_618_, 11);
v_diag_643_ = lean_ctor_get_uint8(v___y_618_, sizeof(void*)*14);
v_cancelTk_x3f_644_ = lean_ctor_get(v___y_618_, 12);
v_suppressElabErrors_645_ = lean_ctor_get_uint8(v___y_618_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_646_ = lean_ctor_get(v___y_618_, 13);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_nat_dec_eq(v_maxRecDepth_635_, v___x_654_);
v___x_656_ = lean_bool_not(v___x_655_);
if (v___x_656_ == 0)
{
v___y_648_ = v___x_656_;
goto v___jp_647_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = lean_nat_dec_eq(v_currRecDepth_634_, v_maxRecDepth_635_);
v___y_648_ = v___x_657_;
goto v___jp_647_;
}
v___jp_621_:
{
if (lean_obj_tag(v___y_622_) == 0)
{
return v___y_622_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___y_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___y_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___y_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___y_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
v___jp_647_:
{
if (v___y_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_currRecDepth_634_, v___x_649_);
lean_inc_ref(v_inheritedTraceOptions_646_);
lean_inc(v_cancelTk_x3f_644_);
lean_inc(v_currMacroScope_642_);
lean_inc(v_quotContext_641_);
lean_inc(v_maxHeartbeats_640_);
lean_inc(v_initHeartbeats_639_);
lean_inc(v_openDecls_638_);
lean_inc(v_currNamespace_637_);
lean_inc(v_ref_636_);
lean_inc(v_maxRecDepth_635_);
lean_inc_ref(v_options_633_);
lean_inc_ref(v_fileMap_632_);
lean_inc_ref(v_fileName_631_);
v___x_651_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_651_, 0, v_fileName_631_);
lean_ctor_set(v___x_651_, 1, v_fileMap_632_);
lean_ctor_set(v___x_651_, 2, v_options_633_);
lean_ctor_set(v___x_651_, 3, v___x_650_);
lean_ctor_set(v___x_651_, 4, v_maxRecDepth_635_);
lean_ctor_set(v___x_651_, 5, v_ref_636_);
lean_ctor_set(v___x_651_, 6, v_currNamespace_637_);
lean_ctor_set(v___x_651_, 7, v_openDecls_638_);
lean_ctor_set(v___x_651_, 8, v_initHeartbeats_639_);
lean_ctor_set(v___x_651_, 9, v_maxHeartbeats_640_);
lean_ctor_set(v___x_651_, 10, v_quotContext_641_);
lean_ctor_set(v___x_651_, 11, v_currMacroScope_642_);
lean_ctor_set(v___x_651_, 12, v_cancelTk_x3f_644_);
lean_ctor_set(v___x_651_, 13, v_inheritedTraceOptions_646_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*14, v_diag_643_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*14 + 1, v_suppressElabErrors_645_);
lean_inc(v___y_619_);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
v___x_652_ = lean_apply_6(v_x_614_, v___y_615_, v___y_616_, v___y_617_, v___x_651_, v___y_619_, lean_box(0));
v___y_622_ = v___x_652_;
goto v___jp_621_;
}
else
{
lean_object* v___x_653_; 
lean_dec_ref(v_x_614_);
lean_inc(v_ref_636_);
v___x_653_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_636_);
v___y_622_ = v___x_653_;
goto v___jp_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_666_, lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_apply_1(v_x_667_, lean_box(0));
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_675_, v_x_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_box(0);
return v___x_685_;
}
else
{
lean_object* v_key_686_; lean_object* v_value_687_; lean_object* v_tail_688_; uint8_t v___x_689_; 
v_key_686_ = lean_ctor_get(v_x_684_, 0);
v_value_687_ = lean_ctor_get(v_x_684_, 1);
v_tail_688_ = lean_ctor_get(v_x_684_, 2);
v___x_689_ = l_Lean_ExprStructEq_beq(v_key_686_, v_a_683_);
if (v___x_689_ == 0)
{
v_x_684_ = v_tail_688_;
goto _start;
}
else
{
lean_object* v___x_691_; 
lean_inc(v_value_687_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_value_687_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_692_, lean_object* v_x_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_692_, v_x_693_);
lean_dec(v_x_693_);
lean_dec_ref(v_a_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_buckets_697_; lean_object* v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v_fold_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_buckets_697_ = lean_ctor_get(v_m_695_, 1);
v___x_698_ = lean_array_get_size(v_buckets_697_);
v___x_699_ = l_Lean_ExprStructEq_hash(v_a_696_);
v___x_700_ = 32ULL;
v___x_701_ = lean_uint64_shift_right(v___x_699_, v___x_700_);
v_fold_702_ = lean_uint64_xor(v___x_699_, v___x_701_);
v___x_703_ = 16ULL;
v___x_704_ = lean_uint64_shift_right(v_fold_702_, v___x_703_);
v___x_705_ = lean_uint64_xor(v_fold_702_, v___x_704_);
v___x_706_ = lean_uint64_to_usize(v___x_705_);
v___x_707_ = lean_usize_of_nat(v___x_698_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_sub(v___x_707_, v___x_708_);
v___x_710_ = lean_usize_land(v___x_706_, v___x_709_);
v___x_711_ = lean_array_uget_borrowed(v_buckets_697_, v___x_710_);
v___x_712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_696_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_713_, v_a_714_);
lean_dec_ref(v_a_714_);
lean_dec_ref(v_m_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_716_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_730_, lean_object* v___y_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_731_);
v___x_738_ = lean_apply_7(v_k_730_, v_b_732_, v___y_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_739_, lean_object* v___y_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_739_, v___y_740_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_748_, uint8_t v_bi_749_, lean_object* v_type_750_, lean_object* v_k_751_, uint8_t v_kind_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; 
lean_inc(v___y_753_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_759_, 0, v_k_751_);
lean_closure_set(v___f_759_, 1, v___y_753_);
v___x_760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_748_, v_bi_749_, v_type_750_, v___f_759_, v_kind_752_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
return v___x_760_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_769_, lean_object* v_bi_770_, lean_object* v_type_771_, lean_object* v_k_772_, lean_object* v_kind_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v_bi_boxed_780_; uint8_t v_kind_boxed_781_; lean_object* v_res_782_; 
v_bi_boxed_780_ = lean_unbox(v_bi_770_);
v_kind_boxed_781_ = lean_unbox(v_kind_773_);
v_res_782_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_769_, v_bi_boxed_780_, v_type_771_, v_k_772_, v_kind_boxed_781_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_783_, lean_object* v_type_784_, lean_object* v_val_785_, lean_object* v_k_786_, uint8_t v_nondep_787_, uint8_t v_kind_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___f_795_; lean_object* v___x_796_; 
lean_inc(v___y_789_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_795_, 0, v_k_786_);
lean_closure_set(v___f_795_, 1, v___y_789_);
v___x_796_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_783_, v_type_784_, v_val_785_, v___f_795_, v_nondep_787_, v_kind_788_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
if (lean_obj_tag(v___x_796_) == 0)
{
return v___x_796_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_805_, lean_object* v_type_806_, lean_object* v_val_807_, lean_object* v_k_808_, lean_object* v_nondep_809_, lean_object* v_kind_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_nondep_boxed_817_; uint8_t v_kind_boxed_818_; lean_object* v_res_819_; 
v_nondep_boxed_817_ = lean_unbox(v_nondep_809_);
v_kind_boxed_818_ = lean_unbox(v_kind_810_);
v_res_819_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_805_, v_type_806_, v_val_807_, v_k_808_, v_nondep_boxed_817_, v_kind_boxed_818_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_823_, lean_object* v_pre_824_, lean_object* v_post_825_, uint8_t v_usedLetOnly_826_, uint8_t v_skipConstInApp_827_, uint8_t v_skipInstances_828_, lean_object* v_body_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_array_push(v_fvars_823_, v_x_830_);
v___x_838_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_824_, v_post_825_, v_usedLetOnly_826_, v_skipConstInApp_827_, v_skipInstances_828_, v___x_837_, v_body_829_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_839_, lean_object* v_pre_840_, lean_object* v_post_841_, lean_object* v_usedLetOnly_842_, lean_object* v_skipConstInApp_843_, lean_object* v_skipInstances_844_, lean_object* v_body_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_usedLetOnly_boxed_853_; uint8_t v_skipConstInApp_boxed_854_; uint8_t v_skipInstances_boxed_855_; lean_object* v_res_856_; 
v_usedLetOnly_boxed_853_ = lean_unbox(v_usedLetOnly_842_);
v_skipConstInApp_boxed_854_ = lean_unbox(v_skipConstInApp_843_);
v_skipInstances_boxed_855_ = lean_unbox(v_skipInstances_844_);
v_res_856_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_839_, v_pre_840_, v_post_841_, v_usedLetOnly_boxed_853_, v_skipConstInApp_boxed_854_, v_skipInstances_boxed_855_, v_body_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_857_, lean_object* v_post_858_, uint8_t v_usedLetOnly_859_, uint8_t v_skipConstInApp_860_, uint8_t v_skipInstances_861_, lean_object* v_e_862_, lean_object* v_a_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
lean_inc_ref(v_post_858_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc_ref(v_e_862_);
v___x_869_ = lean_apply_6(v_post_858_, v_e_862_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_888_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_888_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_888_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_888_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
switch(lean_obj_tag(v_a_870_))
{
case 0:
{
lean_object* v_e_874_; lean_object* v___x_876_; 
lean_dec_ref(v_e_862_);
lean_dec_ref(v_post_858_);
lean_dec_ref(v_pre_857_);
v_e_874_ = lean_ctor_get(v_a_870_, 0);
lean_inc_ref(v_e_874_);
lean_dec_ref_known(v_a_870_, 1);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_e_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_e_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
case 1:
{
lean_object* v_e_878_; lean_object* v___x_879_; 
lean_del_object(v___x_872_);
lean_dec_ref(v_e_862_);
v_e_878_ = lean_ctor_get(v_a_870_, 0);
lean_inc_ref(v_e_878_);
lean_dec_ref_known(v_a_870_, 1);
v___x_879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_857_, v_post_858_, v_usedLetOnly_859_, v_skipConstInApp_860_, v_skipInstances_861_, v_e_878_, v_a_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_879_;
}
default: 
{
lean_object* v_e_x3f_880_; 
lean_dec_ref(v_post_858_);
lean_dec_ref(v_pre_857_);
v_e_x3f_880_ = lean_ctor_get(v_a_870_, 0);
lean_inc(v_e_x3f_880_);
lean_dec_ref_known(v_a_870_, 1);
if (lean_obj_tag(v_e_x3f_880_) == 0)
{
lean_object* v___x_882_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_e_862_);
v___x_882_ = v___x_872_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_e_862_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
lean_object* v_val_884_; lean_object* v___x_886_; 
lean_dec_ref(v_e_862_);
v_val_884_ = lean_ctor_get(v_e_x3f_880_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_e_x3f_880_, 1);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_val_884_);
v___x_886_ = v___x_872_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_val_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v_e_862_);
lean_dec_ref(v_post_858_);
lean_dec_ref(v_pre_857_);
v_a_889_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_869_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_869_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_897_, lean_object* v_post_898_, uint8_t v_usedLetOnly_899_, uint8_t v_skipConstInApp_900_, uint8_t v_skipInstances_901_, lean_object* v_fvars_902_, lean_object* v_e_903_, lean_object* v_a_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
if (lean_obj_tag(v_e_903_) == 6)
{
lean_object* v_binderName_910_; lean_object* v_binderType_911_; lean_object* v_body_912_; uint8_t v_binderInfo_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_binderName_910_ = lean_ctor_get(v_e_903_, 0);
lean_inc(v_binderName_910_);
v_binderType_911_ = lean_ctor_get(v_e_903_, 1);
lean_inc_ref(v_binderType_911_);
v_body_912_ = lean_ctor_get(v_e_903_, 2);
lean_inc_ref(v_body_912_);
v_binderInfo_913_ = lean_ctor_get_uint8(v_e_903_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_903_, 3);
v___x_914_ = lean_expr_instantiate_rev(v_binderType_911_, v_fvars_902_);
lean_dec_ref(v_binderType_911_);
lean_inc_ref(v_post_898_);
lean_inc_ref(v_pre_897_);
v___x_915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_897_, v_post_898_, v_usedLetOnly_899_, v_skipConstInApp_900_, v_skipInstances_901_, v___x_914_, v_a_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___f_920_; uint8_t v___x_921_; lean_object* v___x_922_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = lean_box(v_usedLetOnly_899_);
v___x_918_ = lean_box(v_skipConstInApp_900_);
v___x_919_ = lean_box(v_skipInstances_901_);
v___f_920_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_920_, 0, v_fvars_902_);
lean_closure_set(v___f_920_, 1, v_pre_897_);
lean_closure_set(v___f_920_, 2, v_post_898_);
lean_closure_set(v___f_920_, 3, v___x_917_);
lean_closure_set(v___f_920_, 4, v___x_918_);
lean_closure_set(v___f_920_, 5, v___x_919_);
lean_closure_set(v___f_920_, 6, v_body_912_);
v___x_921_ = 0;
v___x_922_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_910_, v_binderInfo_913_, v_a_916_, v___f_920_, v___x_921_, v_a_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_922_;
}
else
{
lean_dec_ref(v_body_912_);
lean_dec(v_binderName_910_);
lean_dec_ref(v_fvars_902_);
lean_dec_ref(v_post_898_);
lean_dec_ref(v_pre_897_);
return v___x_915_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_expr_instantiate_rev(v_e_903_, v_fvars_902_);
lean_dec_ref(v_e_903_);
lean_inc_ref(v_post_898_);
lean_inc_ref(v_pre_897_);
v___x_924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_897_, v_post_898_, v_usedLetOnly_899_, v_skipConstInApp_900_, v_skipInstances_901_, v___x_923_, v_a_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; uint8_t v___x_926_; uint8_t v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = 0;
v___x_927_ = 1;
v___x_928_ = 1;
v___x_929_ = l_Lean_Meta_mkLambdaFVars(v_fvars_902_, v_a_925_, v___x_926_, v_usedLetOnly_899_, v___x_926_, v___x_927_, v___x_928_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec_ref(v_fvars_902_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_897_, v_post_898_, v_usedLetOnly_899_, v_skipConstInApp_900_, v_skipInstances_901_, v_a_930_, v_a_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_931_;
}
else
{
lean_dec_ref(v_post_898_);
lean_dec_ref(v_pre_897_);
return v___x_929_;
}
}
else
{
lean_dec_ref(v_fvars_902_);
lean_dec_ref(v_post_898_);
lean_dec_ref(v_pre_897_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_932_, lean_object* v_pre_933_, lean_object* v_post_934_, uint8_t v_usedLetOnly_935_, uint8_t v_skipConstInApp_936_, uint8_t v_skipInstances_937_, lean_object* v_body_938_, lean_object* v_x_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_array_push(v_fvars_932_, v_x_939_);
v___x_947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_933_, v_post_934_, v_usedLetOnly_935_, v_skipConstInApp_936_, v_skipInstances_937_, v___x_946_, v_body_938_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_948_, lean_object* v_pre_949_, lean_object* v_post_950_, lean_object* v_usedLetOnly_951_, lean_object* v_skipConstInApp_952_, lean_object* v_skipInstances_953_, lean_object* v_body_954_, lean_object* v_x_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
uint8_t v_usedLetOnly_boxed_962_; uint8_t v_skipConstInApp_boxed_963_; uint8_t v_skipInstances_boxed_964_; lean_object* v_res_965_; 
v_usedLetOnly_boxed_962_ = lean_unbox(v_usedLetOnly_951_);
v_skipConstInApp_boxed_963_ = lean_unbox(v_skipConstInApp_952_);
v_skipInstances_boxed_964_ = lean_unbox(v_skipInstances_953_);
v_res_965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_948_, v_pre_949_, v_post_950_, v_usedLetOnly_boxed_962_, v_skipConstInApp_boxed_963_, v_skipInstances_boxed_964_, v_body_954_, v_x_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_966_, lean_object* v_post_967_, uint8_t v_usedLetOnly_968_, uint8_t v_skipConstInApp_969_, uint8_t v_skipInstances_970_, lean_object* v_fvars_971_, lean_object* v_e_972_, lean_object* v_a_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
if (lean_obj_tag(v_e_972_) == 8)
{
lean_object* v_declName_979_; lean_object* v_type_980_; lean_object* v_value_981_; lean_object* v_body_982_; uint8_t v_nondep_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_declName_979_ = lean_ctor_get(v_e_972_, 0);
lean_inc(v_declName_979_);
v_type_980_ = lean_ctor_get(v_e_972_, 1);
lean_inc_ref(v_type_980_);
v_value_981_ = lean_ctor_get(v_e_972_, 2);
lean_inc_ref(v_value_981_);
v_body_982_ = lean_ctor_get(v_e_972_, 3);
lean_inc_ref(v_body_982_);
v_nondep_983_ = lean_ctor_get_uint8(v_e_972_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_972_, 4);
v___x_984_ = lean_expr_instantiate_rev(v_type_980_, v_fvars_971_);
lean_dec_ref(v_type_980_);
lean_inc_ref(v_post_967_);
lean_inc_ref(v_pre_966_);
v___x_985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_966_, v_post_967_, v_usedLetOnly_968_, v_skipConstInApp_969_, v_skipInstances_970_, v___x_984_, v_a_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = lean_expr_instantiate_rev(v_value_981_, v_fvars_971_);
lean_dec_ref(v_value_981_);
lean_inc_ref(v_post_967_);
lean_inc_ref(v_pre_966_);
v___x_988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_966_, v_post_967_, v_usedLetOnly_968_, v_skipConstInApp_969_, v_skipInstances_970_, v___x_987_, v_a_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___f_993_; uint8_t v___x_994_; lean_object* v___x_995_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = lean_box(v_usedLetOnly_968_);
v___x_991_ = lean_box(v_skipConstInApp_969_);
v___x_992_ = lean_box(v_skipInstances_970_);
v___f_993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_993_, 0, v_fvars_971_);
lean_closure_set(v___f_993_, 1, v_pre_966_);
lean_closure_set(v___f_993_, 2, v_post_967_);
lean_closure_set(v___f_993_, 3, v___x_990_);
lean_closure_set(v___f_993_, 4, v___x_991_);
lean_closure_set(v___f_993_, 5, v___x_992_);
lean_closure_set(v___f_993_, 6, v_body_982_);
v___x_994_ = 0;
v___x_995_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_979_, v_a_986_, v_a_989_, v___f_993_, v_nondep_983_, v___x_994_, v_a_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_995_;
}
else
{
lean_dec(v_a_986_);
lean_dec_ref(v_body_982_);
lean_dec(v_declName_979_);
lean_dec_ref(v_fvars_971_);
lean_dec_ref(v_post_967_);
lean_dec_ref(v_pre_966_);
return v___x_988_;
}
}
else
{
lean_dec_ref(v_body_982_);
lean_dec_ref(v_value_981_);
lean_dec(v_declName_979_);
lean_dec_ref(v_fvars_971_);
lean_dec_ref(v_post_967_);
lean_dec_ref(v_pre_966_);
return v___x_985_;
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_expr_instantiate_rev(v_e_972_, v_fvars_971_);
lean_dec_ref(v_e_972_);
lean_inc_ref(v_post_967_);
lean_inc_ref(v_pre_966_);
v___x_997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_966_, v_post_967_, v_usedLetOnly_968_, v_skipConstInApp_969_, v_skipInstances_970_, v___x_996_, v_a_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; uint8_t v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = 0;
v___x_1000_ = 1;
v___x_1001_ = l_Lean_Meta_mkLetFVars(v_fvars_971_, v_a_998_, v_usedLetOnly_968_, v___x_999_, v___x_1000_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec_ref(v_fvars_971_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_966_, v_post_967_, v_usedLetOnly_968_, v_skipConstInApp_969_, v_skipInstances_970_, v_a_1002_, v_a_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_1003_;
}
else
{
lean_dec_ref(v_post_967_);
lean_dec_ref(v_pre_966_);
return v___x_1001_;
}
}
else
{
lean_dec_ref(v_fvars_971_);
lean_dec_ref(v_post_967_);
lean_dec_ref(v_pre_966_);
return v___x_997_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v_dummy_1005_; 
v___x_1004_ = lean_box(0);
v_dummy_1005_ = l_Lean_Expr_sort___override(v___x_1004_);
return v_dummy_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_1006_, lean_object* v_post_1007_, uint8_t v_usedLetOnly_1008_, uint8_t v_skipConstInApp_1009_, uint8_t v_skipInstances_1010_, size_t v_sz_1011_, size_t v_i_1012_, lean_object* v_bs_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1012_, v_sz_1011_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_post_1007_);
lean_dec_ref(v_pre_1006_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_bs_1013_);
return v___x_1021_;
}
else
{
lean_object* v_v_1022_; lean_object* v___x_1023_; 
v_v_1022_ = lean_array_uget_borrowed(v_bs_1013_, v_i_1012_);
lean_inc(v_v_1022_);
lean_inc_ref(v_post_1007_);
lean_inc_ref(v_pre_1006_);
v___x_1023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1006_, v_post_1007_, v_usedLetOnly_1008_, v_skipConstInApp_1009_, v_skipInstances_1010_, v_v_1022_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v_bs_x27_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = lean_unsigned_to_nat(0u);
v_bs_x27_1026_ = lean_array_uset(v_bs_1013_, v_i_1012_, v___x_1025_);
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1012_, v___x_1027_);
v___x_1029_ = lean_array_uset(v_bs_x27_1026_, v_i_1012_, v_a_1024_);
v_i_1012_ = v___x_1028_;
v_bs_1013_ = v___x_1029_;
goto _start;
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_bs_1013_);
lean_dec_ref(v_post_1007_);
lean_dec_ref(v_pre_1006_);
v_a_1031_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1023_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1023_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1039_, lean_object* v_post_1040_, uint8_t v_usedLetOnly_1041_, uint8_t v_skipConstInApp_1042_, uint8_t v_skipInstances_1043_, lean_object* v___x_1044_, lean_object* v___y_1045_, lean_object* v_b_1046_, lean_object* v_a_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1039_, v_post_1040_, v_usedLetOnly_1041_, v_skipConstInApp_1042_, v_skipInstances_1043_, v___x_1044_, v___y_1045_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1063_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = lean_array_fset(v_b_1046_, v_a_1047_, v_a_1054_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_b_1046_);
v_a_1064_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1053_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1053_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1072_, lean_object* v_post_1073_, lean_object* v_usedLetOnly_1074_, lean_object* v_skipConstInApp_1075_, lean_object* v_skipInstances_1076_, lean_object* v___x_1077_, lean_object* v___y_1078_, lean_object* v_b_1079_, lean_object* v_a_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_usedLetOnly_boxed_1086_; uint8_t v_skipConstInApp_boxed_1087_; uint8_t v_skipInstances_boxed_1088_; lean_object* v_res_1089_; 
v_usedLetOnly_boxed_1086_ = lean_unbox(v_usedLetOnly_1074_);
v_skipConstInApp_boxed_1087_ = lean_unbox(v_skipConstInApp_1075_);
v_skipInstances_boxed_1088_ = lean_unbox(v_skipInstances_1076_);
v_res_1089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1072_, v_post_1073_, v_usedLetOnly_boxed_1086_, v_skipConstInApp_boxed_1087_, v_skipInstances_boxed_1088_, v___x_1077_, v___y_1078_, v_b_1079_, v_a_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v_a_1080_);
lean_dec(v___y_1078_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1090_, lean_object* v___x_1091_, lean_object* v_pre_1092_, lean_object* v_post_1093_, uint8_t v_usedLetOnly_1094_, uint8_t v_skipConstInApp_1095_, uint8_t v_skipInstances_1096_, lean_object* v_a_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___y_1106_; uint8_t v___x_1129_; 
v___x_1129_ = lean_nat_dec_lt(v_a_1097_, v_upperBound_1090_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec(v_a_1097_);
lean_dec_ref(v_post_1093_);
lean_dec_ref(v_pre_1092_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_b_1098_);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = lean_array_fget_borrowed(v_b_1098_, v_a_1097_);
v___x_1132_ = lean_array_get_size(v___x_1091_);
v___x_1133_ = lean_nat_dec_lt(v_a_1097_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___f_1137_; 
lean_inc(v___x_1131_);
v___x_1134_ = lean_box(v_usedLetOnly_1094_);
v___x_1135_ = lean_box(v_skipConstInApp_1095_);
v___x_1136_ = lean_box(v_skipInstances_1096_);
lean_inc(v_a_1097_);
lean_inc(v___y_1099_);
lean_inc_ref(v_post_1093_);
lean_inc_ref(v_pre_1092_);
v___f_1137_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1137_, 0, v_pre_1092_);
lean_closure_set(v___f_1137_, 1, v_post_1093_);
lean_closure_set(v___f_1137_, 2, v___x_1134_);
lean_closure_set(v___f_1137_, 3, v___x_1135_);
lean_closure_set(v___f_1137_, 4, v___x_1136_);
lean_closure_set(v___f_1137_, 5, v___x_1131_);
lean_closure_set(v___f_1137_, 6, v___y_1099_);
lean_closure_set(v___f_1137_, 7, v_b_1098_);
lean_closure_set(v___f_1137_, 8, v_a_1097_);
v___y_1106_ = v___f_1137_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1138_; uint8_t v_isInstance_1139_; 
v___x_1138_ = lean_array_fget_borrowed(v___x_1091_, v_a_1097_);
v_isInstance_1139_ = lean_ctor_get_uint8(v___x_1138_, sizeof(void*)*1 + 4);
if (v_isInstance_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; 
lean_inc(v___x_1131_);
v___x_1140_ = lean_box(v_usedLetOnly_1094_);
v___x_1141_ = lean_box(v_skipConstInApp_1095_);
v___x_1142_ = lean_box(v_skipInstances_1096_);
lean_inc(v_a_1097_);
lean_inc(v___y_1099_);
lean_inc_ref(v_post_1093_);
lean_inc_ref(v_pre_1092_);
v___f_1143_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1143_, 0, v_pre_1092_);
lean_closure_set(v___f_1143_, 1, v_post_1093_);
lean_closure_set(v___f_1143_, 2, v___x_1140_);
lean_closure_set(v___f_1143_, 3, v___x_1141_);
lean_closure_set(v___f_1143_, 4, v___x_1142_);
lean_closure_set(v___f_1143_, 5, v___x_1131_);
lean_closure_set(v___f_1143_, 6, v___y_1099_);
lean_closure_set(v___f_1143_, 7, v_b_1098_);
lean_closure_set(v___f_1143_, 8, v_a_1097_);
v___y_1106_ = v___f_1143_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1144_; lean_object* v___f_1145_; 
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_b_1098_);
v___f_1145_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1145_, 0, v___x_1144_);
v___y_1106_ = v___f_1145_;
goto v___jp_1105_;
}
}
}
v___jp_1105_:
{
lean_object* v___x_1107_; 
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
v___x_1107_ = lean_apply_5(v___y_1106_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1120_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
if (lean_obj_tag(v_a_1108_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; 
lean_dec(v_a_1097_);
lean_dec_ref(v_post_1093_);
lean_dec_ref(v_pre_1092_);
v_a_1112_ = lean_ctor_get(v_a_1108_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v_a_1108_, 1);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v_a_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_del_object(v___x_1110_);
v_a_1116_ = lean_ctor_get(v_a_1108_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v_a_1108_, 1);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_a_1097_, v___x_1117_);
lean_dec(v_a_1097_);
v_a_1097_ = v___x_1118_;
v_b_1098_ = v_a_1116_;
goto _start;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1097_);
lean_dec_ref(v_post_1093_);
lean_dec_ref(v_pre_1092_);
v_a_1121_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1107_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1107_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1146_, lean_object* v_pre_1147_, lean_object* v_post_1148_, uint8_t v_usedLetOnly_1149_, uint8_t v_skipConstInApp_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_f_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; 
if (lean_obj_tag(v_x_1151_) == 5)
{
lean_object* v_fn_1209_; lean_object* v_arg_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_fn_1209_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_fn_1209_);
v_arg_1210_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_arg_1210_);
lean_dec_ref_known(v_x_1151_, 2);
v___x_1211_ = lean_array_set(v_x_1152_, v_x_1153_, v_arg_1210_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_sub(v_x_1153_, v___x_1212_);
lean_dec(v_x_1153_);
v_x_1151_ = v_fn_1209_;
v_x_1152_ = v___x_1211_;
v_x_1153_ = v___x_1213_;
goto _start;
}
else
{
lean_dec(v_x_1153_);
if (v_skipConstInApp_1150_ == 0)
{
goto v___jp_1206_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = l_Lean_Expr_isConst(v_x_1151_);
if (v___x_1215_ == 0)
{
goto v___jp_1206_;
}
else
{
v_f_1161_ = v_x_1151_;
v___y_1162_ = v___y_1154_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___y_1156_;
v___y_1165_ = v___y_1157_;
v___y_1166_ = v___y_1158_;
goto v___jp_1160_;
}
}
}
v___jp_1160_:
{
if (v_skipInstances_1146_ == 0)
{
size_t v_sz_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
v_sz_1167_ = lean_array_size(v_x_1152_);
v___x_1168_ = ((size_t)0ULL);
lean_inc_ref(v_post_1148_);
lean_inc_ref(v_pre_1147_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1147_, v_post_1148_, v_usedLetOnly_1149_, v_skipConstInApp_1150_, v_skipInstances_1146_, v_sz_1167_, v___x_1168_, v_x_1152_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = l_Lean_mkAppN(v_f_1161_, v_a_1170_);
lean_dec(v_a_1170_);
v___x_1172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1147_, v_post_1148_, v_usedLetOnly_1149_, v_skipConstInApp_1150_, v_skipInstances_1146_, v___x_1171_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1172_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_f_1161_);
lean_dec_ref(v_post_1148_);
lean_dec_ref(v_pre_1147_);
v_a_1173_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1169_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1169_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_x_1152_);
lean_inc_ref(v_f_1161_);
v___x_1182_ = l_Lean_Meta_getFunInfoNArgs(v_f_1161_, v___x_1181_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v_paramInfo_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v_paramInfo_1184_ = lean_ctor_get(v_a_1183_, 0);
lean_inc_ref(v_paramInfo_1184_);
lean_dec(v_a_1183_);
v___x_1185_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1148_);
lean_inc_ref(v_pre_1147_);
v___x_1186_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1181_, v_paramInfo_1184_, v_pre_1147_, v_post_1148_, v_usedLetOnly_1149_, v_skipConstInApp_1150_, v_skipInstances_1146_, v___x_1185_, v_x_1152_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v_paramInfo_1184_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = l_Lean_mkAppN(v_f_1161_, v_a_1187_);
lean_dec(v_a_1187_);
v___x_1189_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1147_, v_post_1148_, v_usedLetOnly_1149_, v_skipConstInApp_1150_, v_skipInstances_1146_, v___x_1188_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1189_;
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_f_1161_);
lean_dec_ref(v_post_1148_);
lean_dec_ref(v_pre_1147_);
v_a_1190_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1186_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1186_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_f_1161_);
lean_dec_ref(v_x_1152_);
lean_dec_ref(v_post_1148_);
lean_dec_ref(v_pre_1147_);
v_a_1198_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1182_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1182_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
v___jp_1206_:
{
lean_object* v___x_1207_; 
lean_inc_ref(v_post_1148_);
lean_inc_ref(v_pre_1147_);
v___x_1207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1147_, v_post_1148_, v_usedLetOnly_1149_, v_skipConstInApp_1150_, v_skipInstances_1146_, v_x_1151_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v_f_1161_ = v_a_1208_;
v___y_1162_ = v___y_1154_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___y_1156_;
v___y_1165_ = v___y_1157_;
v___y_1166_ = v___y_1158_;
goto v___jp_1160_;
}
else
{
lean_dec_ref(v_x_1152_);
lean_dec_ref(v_post_1148_);
lean_dec_ref(v_pre_1147_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1216_, lean_object* v_pre_1217_, lean_object* v_e_1218_, lean_object* v_post_1219_, uint8_t v_usedLetOnly_1220_, uint8_t v_skipConstInApp_1221_, uint8_t v_skipInstances_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Core_checkSystem(v___x_1216_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref_known(v___x_1229_, 1);
lean_inc_ref(v_pre_1217_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc_ref(v_e_1218_);
v___x_1230_ = lean_apply_6(v_pre_1217_, v_e_1218_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1279_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1279_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1279_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___y_1236_; 
switch(lean_obj_tag(v_a_1231_))
{
case 0:
{
lean_object* v_e_1271_; lean_object* v___x_1273_; 
lean_dec_ref(v_post_1219_);
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_pre_1217_);
v_e_1271_ = lean_ctor_get(v_a_1231_, 0);
lean_inc_ref(v_e_1271_);
lean_dec_ref_known(v_a_1231_, 1);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_e_1271_);
v___x_1273_ = v___x_1233_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_e_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
case 1:
{
lean_object* v_e_1275_; lean_object* v___x_1276_; 
lean_del_object(v___x_1233_);
lean_dec_ref(v_e_1218_);
v_e_1275_ = lean_ctor_get(v_a_1231_, 0);
lean_inc_ref(v_e_1275_);
lean_dec_ref_known(v_a_1231_, 1);
v___x_1276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v_e_1275_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1276_;
}
default: 
{
lean_object* v_e_x3f_1277_; 
lean_del_object(v___x_1233_);
v_e_x3f_1277_ = lean_ctor_get(v_a_1231_, 0);
lean_inc(v_e_x3f_1277_);
lean_dec_ref_known(v_a_1231_, 1);
if (lean_obj_tag(v_e_x3f_1277_) == 0)
{
v___y_1236_ = v_e_1218_;
goto v___jp_1235_;
}
else
{
lean_object* v_val_1278_; 
lean_dec_ref(v_e_1218_);
v_val_1278_ = lean_ctor_get(v_e_x3f_1277_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v_e_x3f_1277_, 1);
v___y_1236_ = v_val_1278_;
goto v___jp_1235_;
}
}
}
v___jp_1235_:
{
switch(lean_obj_tag(v___y_1236_))
{
case 7:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___x_1237_, v___y_1236_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1238_;
}
case 6:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___x_1239_, v___y_1236_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1240_;
}
case 8:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1242_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___x_1241_, v___y_1236_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1242_;
}
case 5:
{
lean_object* v_dummy_1243_; lean_object* v_nargs_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_dummy_1243_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1244_ = l_Lean_Expr_getAppNumArgs(v___y_1236_);
lean_inc(v_nargs_1244_);
v___x_1245_ = lean_mk_array(v_nargs_1244_, v_dummy_1243_);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_sub(v_nargs_1244_, v___x_1246_);
lean_dec(v_nargs_1244_);
v___x_1248_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1222_, v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v___y_1236_, v___x_1245_, v___x_1247_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1248_;
}
case 10:
{
lean_object* v_data_1249_; lean_object* v_expr_1250_; lean_object* v___x_1251_; 
v_data_1249_ = lean_ctor_get(v___y_1236_, 0);
v_expr_1250_ = lean_ctor_get(v___y_1236_, 1);
lean_inc_ref(v_expr_1250_);
lean_inc_ref(v_post_1219_);
lean_inc_ref(v_pre_1217_);
v___x_1251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v_expr_1250_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; size_t v___x_1253_; size_t v___x_1254_; uint8_t v___x_1255_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_ptr_addr(v_expr_1250_);
v___x_1254_ = lean_ptr_addr(v_a_1252_);
v___x_1255_ = lean_usize_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc(v_data_1249_);
lean_dec_ref_known(v___y_1236_, 2);
v___x_1256_ = l_Lean_Expr_mdata___override(v_data_1249_, v_a_1252_);
v___x_1257_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___x_1256_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; 
lean_dec(v_a_1252_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___y_1236_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1258_;
}
}
else
{
lean_dec_ref_known(v___y_1236_, 2);
lean_dec_ref(v_post_1219_);
lean_dec_ref(v_pre_1217_);
return v___x_1251_;
}
}
case 11:
{
lean_object* v_typeName_1259_; lean_object* v_idx_1260_; lean_object* v_struct_1261_; lean_object* v___x_1262_; 
v_typeName_1259_ = lean_ctor_get(v___y_1236_, 0);
v_idx_1260_ = lean_ctor_get(v___y_1236_, 1);
v_struct_1261_ = lean_ctor_get(v___y_1236_, 2);
lean_inc_ref(v_struct_1261_);
lean_inc_ref(v_post_1219_);
lean_inc_ref(v_pre_1217_);
v___x_1262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v_struct_1261_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; size_t v___x_1264_; size_t v___x_1265_; uint8_t v___x_1266_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_ptr_addr(v_struct_1261_);
v___x_1265_ = lean_ptr_addr(v_a_1263_);
v___x_1266_ = lean_usize_dec_eq(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_inc(v_idx_1260_);
lean_inc(v_typeName_1259_);
lean_dec_ref_known(v___y_1236_, 3);
v___x_1267_ = l_Lean_Expr_proj___override(v_typeName_1259_, v_idx_1260_, v_a_1263_);
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___x_1267_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_a_1263_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___y_1236_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1269_;
}
}
else
{
lean_dec_ref_known(v___y_1236_, 3);
lean_dec_ref(v_post_1219_);
lean_dec_ref(v_pre_1217_);
return v___x_1262_;
}
}
default: 
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1217_, v_post_1219_, v_usedLetOnly_1220_, v_skipConstInApp_1221_, v_skipInstances_1222_, v___y_1236_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1270_;
}
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_post_1219_);
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_pre_1217_);
v_a_1280_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1230_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1230_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_post_1219_);
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_pre_1217_);
v_a_1288_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1229_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1229_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1296_, lean_object* v_pre_1297_, lean_object* v_e_1298_, lean_object* v_post_1299_, lean_object* v_usedLetOnly_1300_, lean_object* v_skipConstInApp_1301_, lean_object* v_skipInstances_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v_usedLetOnly_boxed_1309_; uint8_t v_skipConstInApp_boxed_1310_; uint8_t v_skipInstances_boxed_1311_; lean_object* v_res_1312_; 
v_usedLetOnly_boxed_1309_ = lean_unbox(v_usedLetOnly_1300_);
v_skipConstInApp_boxed_1310_ = lean_unbox(v_skipConstInApp_1301_);
v_skipInstances_boxed_1311_ = lean_unbox(v_skipInstances_1302_);
v_res_1312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1296_, v_pre_1297_, v_e_1298_, v_post_1299_, v_usedLetOnly_boxed_1309_, v_skipConstInApp_boxed_1310_, v_skipInstances_boxed_1311_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1313_, lean_object* v_post_1314_, uint8_t v_usedLetOnly_1315_, uint8_t v_skipConstInApp_1316_, uint8_t v_skipInstances_1317_, lean_object* v_e_1318_, lean_object* v_a_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_inc(v_a_1319_);
v___x_1325_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1325_, 0, lean_box(0));
lean_closure_set(v___x_1325_, 1, lean_box(0));
lean_closure_set(v___x_1325_, 2, v_a_1319_);
v___x_1326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1325_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1361_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1361_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1361_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1327_, v_e_1318_);
lean_dec(v_a_1327_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; 
lean_del_object(v___x_1329_);
v___x_1332_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1333_ = lean_box(v_usedLetOnly_1315_);
v___x_1334_ = lean_box(v_skipConstInApp_1316_);
v___x_1335_ = lean_box(v_skipInstances_1317_);
lean_inc_ref(v_e_1318_);
v___f_1336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1336_, 0, v___x_1332_);
lean_closure_set(v___f_1336_, 1, v_pre_1313_);
lean_closure_set(v___f_1336_, 2, v_e_1318_);
lean_closure_set(v___f_1336_, 3, v_post_1314_);
lean_closure_set(v___f_1336_, 4, v___x_1333_);
lean_closure_set(v___f_1336_, 5, v___x_1334_);
lean_closure_set(v___f_1336_, 6, v___x_1335_);
v___x_1337_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1336_, v_a_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc_n(v_a_1338_, 2);
lean_dec_ref_known(v___x_1337_, 1);
lean_inc(v_a_1319_);
v___f_1339_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1339_, 0, v_a_1319_);
lean_closure_set(v___f_1339_, 1, v_e_1318_);
lean_closure_set(v___f_1339_, 2, v_a_1338_);
v___x_1340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1339_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1348_);
v___x_1342_ = v___x_1340_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___x_1340_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v_a_1338_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1338_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1338_);
v_a_1349_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1340_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_dec_ref(v_e_1318_);
return v___x_1337_;
}
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1359_; 
lean_dec_ref(v_e_1318_);
lean_dec_ref(v_post_1314_);
lean_dec_ref(v_pre_1313_);
v_val_1357_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v___x_1331_, 1);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_val_1357_);
v___x_1359_ = v___x_1329_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_val_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_e_1318_);
lean_dec_ref(v_post_1314_);
lean_dec_ref(v_pre_1313_);
v_a_1362_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1326_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1326_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1370_, lean_object* v_pre_1371_, lean_object* v_post_1372_, lean_object* v_usedLetOnly_1373_, lean_object* v_skipConstInApp_1374_, lean_object* v_skipInstances_1375_, lean_object* v_body_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_usedLetOnly_boxed_1384_; uint8_t v_skipConstInApp_boxed_1385_; uint8_t v_skipInstances_boxed_1386_; lean_object* v_res_1387_; 
v_usedLetOnly_boxed_1384_ = lean_unbox(v_usedLetOnly_1373_);
v_skipConstInApp_boxed_1385_ = lean_unbox(v_skipConstInApp_1374_);
v_skipInstances_boxed_1386_ = lean_unbox(v_skipInstances_1375_);
v_res_1387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1370_, v_pre_1371_, v_post_1372_, v_usedLetOnly_boxed_1384_, v_skipConstInApp_boxed_1385_, v_skipInstances_boxed_1386_, v_body_1376_, v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1388_, lean_object* v_post_1389_, uint8_t v_usedLetOnly_1390_, uint8_t v_skipConstInApp_1391_, uint8_t v_skipInstances_1392_, lean_object* v_fvars_1393_, lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
if (lean_obj_tag(v_e_1394_) == 7)
{
lean_object* v_binderName_1401_; lean_object* v_binderType_1402_; lean_object* v_body_1403_; uint8_t v_binderInfo_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_binderName_1401_ = lean_ctor_get(v_e_1394_, 0);
lean_inc(v_binderName_1401_);
v_binderType_1402_ = lean_ctor_get(v_e_1394_, 1);
lean_inc_ref(v_binderType_1402_);
v_body_1403_ = lean_ctor_get(v_e_1394_, 2);
lean_inc_ref(v_body_1403_);
v_binderInfo_1404_ = lean_ctor_get_uint8(v_e_1394_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1394_, 3);
v___x_1405_ = lean_expr_instantiate_rev(v_binderType_1402_, v_fvars_1393_);
lean_dec_ref(v_binderType_1402_);
lean_inc_ref(v_post_1389_);
lean_inc_ref(v_pre_1388_);
v___x_1406_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1388_, v_post_1389_, v_usedLetOnly_1390_, v_skipConstInApp_1391_, v_skipInstances_1392_, v___x_1405_, v_a_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = lean_box(v_usedLetOnly_1390_);
v___x_1409_ = lean_box(v_skipConstInApp_1391_);
v___x_1410_ = lean_box(v_skipInstances_1392_);
v___f_1411_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1411_, 0, v_fvars_1393_);
lean_closure_set(v___f_1411_, 1, v_pre_1388_);
lean_closure_set(v___f_1411_, 2, v_post_1389_);
lean_closure_set(v___f_1411_, 3, v___x_1408_);
lean_closure_set(v___f_1411_, 4, v___x_1409_);
lean_closure_set(v___f_1411_, 5, v___x_1410_);
lean_closure_set(v___f_1411_, 6, v_body_1403_);
v___x_1412_ = 0;
v___x_1413_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1401_, v_binderInfo_1404_, v_a_1407_, v___f_1411_, v___x_1412_, v_a_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1413_;
}
else
{
lean_dec_ref(v_body_1403_);
lean_dec(v_binderName_1401_);
lean_dec_ref(v_fvars_1393_);
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
return v___x_1406_;
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_expr_instantiate_rev(v_e_1394_, v_fvars_1393_);
lean_dec_ref(v_e_1394_);
lean_inc_ref(v_post_1389_);
lean_inc_ref(v_pre_1388_);
v___x_1415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1388_, v_post_1389_, v_usedLetOnly_1390_, v_skipConstInApp_1391_, v_skipInstances_1392_, v___x_1414_, v_a_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = 0;
v___x_1418_ = 1;
v___x_1419_ = 1;
v___x_1420_ = l_Lean_Meta_mkForallFVars(v_fvars_1393_, v_a_1416_, v___x_1417_, v_usedLetOnly_1390_, v___x_1418_, v___x_1419_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref(v_fvars_1393_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1388_, v_post_1389_, v_usedLetOnly_1390_, v_skipConstInApp_1391_, v_skipInstances_1392_, v_a_1421_, v_a_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1422_;
}
else
{
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
return v___x_1420_;
}
}
else
{
lean_dec_ref(v_fvars_1393_);
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1423_, lean_object* v_pre_1424_, lean_object* v_post_1425_, uint8_t v_usedLetOnly_1426_, uint8_t v_skipConstInApp_1427_, uint8_t v_skipInstances_1428_, lean_object* v_body_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_array_push(v_fvars_1423_, v_x_1430_);
v___x_1438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1424_, v_post_1425_, v_usedLetOnly_1426_, v_skipConstInApp_1427_, v_skipInstances_1428_, v___x_1437_, v_body_1429_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1439_, lean_object* v_post_1440_, lean_object* v_usedLetOnly_1441_, lean_object* v_skipConstInApp_1442_, lean_object* v_skipInstances_1443_, lean_object* v_e_1444_, lean_object* v_a_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_usedLetOnly_boxed_1451_; uint8_t v_skipConstInApp_boxed_1452_; uint8_t v_skipInstances_boxed_1453_; lean_object* v_res_1454_; 
v_usedLetOnly_boxed_1451_ = lean_unbox(v_usedLetOnly_1441_);
v_skipConstInApp_boxed_1452_ = lean_unbox(v_skipConstInApp_1442_);
v_skipInstances_boxed_1453_ = lean_unbox(v_skipInstances_1443_);
v_res_1454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1439_, v_post_1440_, v_usedLetOnly_boxed_1451_, v_skipConstInApp_boxed_1452_, v_skipInstances_boxed_1453_, v_e_1444_, v_a_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v_a_1445_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1455_, lean_object* v_post_1456_, lean_object* v_usedLetOnly_1457_, lean_object* v_skipConstInApp_1458_, lean_object* v_skipInstances_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_bs_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_usedLetOnly_boxed_1469_; uint8_t v_skipConstInApp_boxed_1470_; uint8_t v_skipInstances_boxed_1471_; size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_usedLetOnly_boxed_1469_ = lean_unbox(v_usedLetOnly_1457_);
v_skipConstInApp_boxed_1470_ = lean_unbox(v_skipConstInApp_1458_);
v_skipInstances_boxed_1471_ = lean_unbox(v_skipInstances_1459_);
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1455_, v_post_1456_, v_usedLetOnly_boxed_1469_, v_skipConstInApp_boxed_1470_, v_skipInstances_boxed_1471_, v_sz_boxed_1472_, v_i_boxed_1473_, v_bs_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1475_, lean_object* v_post_1476_, lean_object* v_usedLetOnly_1477_, lean_object* v_skipConstInApp_1478_, lean_object* v_skipInstances_1479_, lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v_usedLetOnly_boxed_1487_; uint8_t v_skipConstInApp_boxed_1488_; uint8_t v_skipInstances_boxed_1489_; lean_object* v_res_1490_; 
v_usedLetOnly_boxed_1487_ = lean_unbox(v_usedLetOnly_1477_);
v_skipConstInApp_boxed_1488_ = lean_unbox(v_skipConstInApp_1478_);
v_skipInstances_boxed_1489_ = lean_unbox(v_skipInstances_1479_);
v_res_1490_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1475_, v_post_1476_, v_usedLetOnly_boxed_1487_, v_skipConstInApp_boxed_1488_, v_skipInstances_boxed_1489_, v_e_1480_, v_a_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v_a_1481_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1491_, lean_object* v_post_1492_, lean_object* v_usedLetOnly_1493_, lean_object* v_skipConstInApp_1494_, lean_object* v_skipInstances_1495_, lean_object* v_fvars_1496_, lean_object* v_e_1497_, lean_object* v_a_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_usedLetOnly_boxed_1504_; uint8_t v_skipConstInApp_boxed_1505_; uint8_t v_skipInstances_boxed_1506_; lean_object* v_res_1507_; 
v_usedLetOnly_boxed_1504_ = lean_unbox(v_usedLetOnly_1493_);
v_skipConstInApp_boxed_1505_ = lean_unbox(v_skipConstInApp_1494_);
v_skipInstances_boxed_1506_ = lean_unbox(v_skipInstances_1495_);
v_res_1507_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1491_, v_post_1492_, v_usedLetOnly_boxed_1504_, v_skipConstInApp_boxed_1505_, v_skipInstances_boxed_1506_, v_fvars_1496_, v_e_1497_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v_a_1498_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1508_, lean_object* v_post_1509_, lean_object* v_usedLetOnly_1510_, lean_object* v_skipConstInApp_1511_, lean_object* v_skipInstances_1512_, lean_object* v_fvars_1513_, lean_object* v_e_1514_, lean_object* v_a_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_usedLetOnly_boxed_1521_; uint8_t v_skipConstInApp_boxed_1522_; uint8_t v_skipInstances_boxed_1523_; lean_object* v_res_1524_; 
v_usedLetOnly_boxed_1521_ = lean_unbox(v_usedLetOnly_1510_);
v_skipConstInApp_boxed_1522_ = lean_unbox(v_skipConstInApp_1511_);
v_skipInstances_boxed_1523_ = lean_unbox(v_skipInstances_1512_);
v_res_1524_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1508_, v_post_1509_, v_usedLetOnly_boxed_1521_, v_skipConstInApp_boxed_1522_, v_skipInstances_boxed_1523_, v_fvars_1513_, v_e_1514_, v_a_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v_a_1515_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1525_, lean_object* v_post_1526_, lean_object* v_usedLetOnly_1527_, lean_object* v_skipConstInApp_1528_, lean_object* v_skipInstances_1529_, lean_object* v_fvars_1530_, lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_usedLetOnly_boxed_1538_; uint8_t v_skipConstInApp_boxed_1539_; uint8_t v_skipInstances_boxed_1540_; lean_object* v_res_1541_; 
v_usedLetOnly_boxed_1538_ = lean_unbox(v_usedLetOnly_1527_);
v_skipConstInApp_boxed_1539_ = lean_unbox(v_skipConstInApp_1528_);
v_skipInstances_boxed_1540_ = lean_unbox(v_skipInstances_1529_);
v_res_1541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1525_, v_post_1526_, v_usedLetOnly_boxed_1538_, v_skipConstInApp_boxed_1539_, v_skipInstances_boxed_1540_, v_fvars_1530_, v_e_1531_, v_a_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v_a_1532_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1542_, lean_object* v___x_1543_, lean_object* v_pre_1544_, lean_object* v_post_1545_, lean_object* v_usedLetOnly_1546_, lean_object* v_skipConstInApp_1547_, lean_object* v_skipInstances_1548_, lean_object* v_a_1549_, lean_object* v_b_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v_usedLetOnly_boxed_1557_; uint8_t v_skipConstInApp_boxed_1558_; uint8_t v_skipInstances_boxed_1559_; lean_object* v_res_1560_; 
v_usedLetOnly_boxed_1557_ = lean_unbox(v_usedLetOnly_1546_);
v_skipConstInApp_boxed_1558_ = lean_unbox(v_skipConstInApp_1547_);
v_skipInstances_boxed_1559_ = lean_unbox(v_skipInstances_1548_);
v_res_1560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1542_, v___x_1543_, v_pre_1544_, v_post_1545_, v_usedLetOnly_boxed_1557_, v_skipConstInApp_boxed_1558_, v_skipInstances_boxed_1559_, v_a_1549_, v_b_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___x_1543_);
lean_dec(v_upperBound_1542_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1561_, lean_object* v_pre_1562_, lean_object* v_post_1563_, lean_object* v_usedLetOnly_1564_, lean_object* v_skipConstInApp_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_skipInstances_boxed_1575_; uint8_t v_usedLetOnly_boxed_1576_; uint8_t v_skipConstInApp_boxed_1577_; lean_object* v_res_1578_; 
v_skipInstances_boxed_1575_ = lean_unbox(v_skipInstances_1561_);
v_usedLetOnly_boxed_1576_ = lean_unbox(v_usedLetOnly_1564_);
v_skipConstInApp_boxed_1577_ = lean_unbox(v_skipConstInApp_1565_);
v_res_1578_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1575_, v_pre_1562_, v_post_1563_, v_usedLetOnly_boxed_1576_, v_skipConstInApp_boxed_1577_, v_x_1566_, v_x_1567_, v_x_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
return v_res_1578_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_unsigned_to_nat(16u);
v___x_1581_ = lean_mk_array(v___x_1580_, v___x_1579_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1586_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1586_, 0, lean_box(0));
lean_closure_set(v___x_1586_, 1, lean_box(0));
lean_closure_set(v___x_1586_, 2, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1587_, lean_object* v_pre_1588_, lean_object* v_post_1589_, uint8_t v_usedLetOnly_1590_, uint8_t v_skipConstInApp_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_a_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1597_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1598_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1597_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = 0;
v___x_1601_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1588_, v_post_1589_, v_usedLetOnly_1590_, v_skipConstInApp_1591_, v___x_1600_, v_input_1587_, v_a_1599_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1603_, 0, lean_box(0));
lean_closure_set(v___x_1603_, 1, lean_box(0));
lean_closure_set(v___x_1603_, 2, v_a_1599_);
v___x_1604_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1603_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1612_);
v___x_1606_ = v___x_1604_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v___x_1604_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v_a_1602_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1602_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_dec(v_a_1599_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1613_, lean_object* v_pre_1614_, lean_object* v_post_1615_, lean_object* v_usedLetOnly_1616_, lean_object* v_skipConstInApp_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v_usedLetOnly_boxed_1623_; uint8_t v_skipConstInApp_boxed_1624_; lean_object* v_res_1625_; 
v_usedLetOnly_boxed_1623_ = lean_unbox(v_usedLetOnly_1616_);
v_skipConstInApp_boxed_1624_ = lean_unbox(v_skipConstInApp_1617_);
v_res_1625_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1613_, v_pre_1614_, v_post_1615_, v_usedLetOnly_boxed_1623_, v_skipConstInApp_boxed_1624_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1647_; 
v___x_1634_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1628_, v_a_1632_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1647_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1647_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
uint8_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = lean_unbox(v_a_1635_);
lean_dec(v_a_1635_);
v___x_1640_ = lean_bool_not(v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_del_object(v___x_1637_);
v___f_1641_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1642_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1643_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1628_, v___x_1642_, v___f_1641_, v___x_1640_, v___x_1640_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
return v___x_1643_;
}
else
{
lean_object* v___x_1645_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_e_1628_);
v___x_1645_ = v___x_1637_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_e_1628_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1655_, lean_object* v___x_1656_, lean_object* v_pre_1657_, lean_object* v_post_1658_, uint8_t v_usedLetOnly_1659_, uint8_t v_skipConstInApp_1660_, uint8_t v_skipInstances_1661_, lean_object* v___x_1662_, lean_object* v_inst_1663_, lean_object* v_R_1664_, lean_object* v_a_1665_, lean_object* v_b_1666_, lean_object* v_c_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1655_, v___x_1656_, v_pre_1657_, v_post_1658_, v_usedLetOnly_1659_, v_skipConstInApp_1660_, v_skipInstances_1661_, v_a_1665_, v_b_1666_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1675_ = _args[0];
lean_object* v___x_1676_ = _args[1];
lean_object* v_pre_1677_ = _args[2];
lean_object* v_post_1678_ = _args[3];
lean_object* v_usedLetOnly_1679_ = _args[4];
lean_object* v_skipConstInApp_1680_ = _args[5];
lean_object* v_skipInstances_1681_ = _args[6];
lean_object* v___x_1682_ = _args[7];
lean_object* v_inst_1683_ = _args[8];
lean_object* v_R_1684_ = _args[9];
lean_object* v_a_1685_ = _args[10];
lean_object* v_b_1686_ = _args[11];
lean_object* v_c_1687_ = _args[12];
lean_object* v___y_1688_ = _args[13];
lean_object* v___y_1689_ = _args[14];
lean_object* v___y_1690_ = _args[15];
lean_object* v___y_1691_ = _args[16];
lean_object* v___y_1692_ = _args[17];
lean_object* v___y_1693_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1694_; uint8_t v_skipConstInApp_boxed_1695_; uint8_t v_skipInstances_boxed_1696_; lean_object* v_res_1697_; 
v_usedLetOnly_boxed_1694_ = lean_unbox(v_usedLetOnly_1679_);
v_skipConstInApp_boxed_1695_ = lean_unbox(v_skipConstInApp_1680_);
v_skipInstances_boxed_1696_ = lean_unbox(v_skipInstances_1681_);
v_res_1697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1675_, v___x_1676_, v_pre_1677_, v_post_1678_, v_usedLetOnly_boxed_1694_, v_skipConstInApp_boxed_1695_, v_skipInstances_boxed_1696_, v___x_1682_, v_inst_1683_, v_R_1684_, v_a_1685_, v_b_1686_, v_c_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___x_1682_);
lean_dec_ref(v___x_1676_);
lean_dec(v_upperBound_1675_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1698_, lean_object* v_m_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1699_, v_a_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1702_, lean_object* v_m_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1702_, v_m_1703_, v_a_1704_);
lean_dec_ref(v_a_1704_);
lean_dec_ref(v_m_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1706_, lean_object* v_name_1707_, uint8_t v_bi_1708_, lean_object* v_type_1709_, lean_object* v_k_1710_, uint8_t v_kind_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1707_, v_bi_1708_, v_type_1709_, v_k_1710_, v_kind_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_name_1720_, lean_object* v_bi_1721_, lean_object* v_type_1722_, lean_object* v_k_1723_, lean_object* v_kind_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v_bi_boxed_1731_; uint8_t v_kind_boxed_1732_; lean_object* v_res_1733_; 
v_bi_boxed_1731_ = lean_unbox(v_bi_1721_);
v_kind_boxed_1732_ = lean_unbox(v_kind_1724_);
v_res_1733_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1719_, v_name_1720_, v_bi_boxed_1731_, v_type_1722_, v_k_1723_, v_kind_boxed_1732_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1734_, lean_object* v_name_1735_, lean_object* v_type_1736_, lean_object* v_val_1737_, lean_object* v_k_1738_, uint8_t v_nondep_1739_, uint8_t v_kind_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1735_, v_type_1736_, v_val_1737_, v_k_1738_, v_nondep_1739_, v_kind_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_name_1749_, lean_object* v_type_1750_, lean_object* v_val_1751_, lean_object* v_k_1752_, lean_object* v_nondep_1753_, lean_object* v_kind_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v_nondep_boxed_1761_; uint8_t v_kind_boxed_1762_; lean_object* v_res_1763_; 
v_nondep_boxed_1761_ = lean_unbox(v_nondep_1753_);
v_kind_boxed_1762_ = lean_unbox(v_kind_1754_);
v_res_1763_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1748_, v_name_1749_, v_type_1750_, v_val_1751_, v_k_1752_, v_nondep_boxed_1761_, v_kind_boxed_1762_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1764_, lean_object* v_ref_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1765_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_ref_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1772_, v_ref_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1780_, lean_object* v_x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1789_, v_x_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1798_, lean_object* v_m_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1799_, v_a_1800_, v_b_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1803_, lean_object* v_a_1804_, lean_object* v_x_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1804_, v_x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1807_, lean_object* v_a_1808_, lean_object* v_x_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1807_, v_a_1808_, v_x_1809_);
lean_dec(v_x_1809_);
lean_dec_ref(v_a_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1811_, lean_object* v_a_1812_, lean_object* v_x_1813_){
_start:
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1812_, v_x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1815_, lean_object* v_a_1816_, lean_object* v_x_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1815_, v_a_1816_, v_x_1817_);
lean_dec(v_x_1817_);
lean_dec_ref(v_a_1816_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1820_, lean_object* v_data_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1823_, lean_object* v_a_1824_, lean_object* v_b_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1824_, v_b_1825_, v_x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1828_, lean_object* v_i_1829_, lean_object* v_source_1830_, lean_object* v_target_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1829_, v_source_1830_, v_target_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v_env_1844_; lean_object* v___x_1845_; lean_object* v_mctx_1846_; lean_object* v_lctx_1847_; lean_object* v_options_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1843_ = lean_st_ref_get(v___y_1841_);
v_env_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_env_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = lean_st_ref_get(v___y_1839_);
v_mctx_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_ref(v_mctx_1846_);
lean_dec(v___x_1845_);
v_lctx_1847_ = lean_ctor_get(v___y_1838_, 2);
v_options_1848_ = lean_ctor_get(v___y_1840_, 2);
lean_inc_ref(v_options_1848_);
lean_inc_ref(v_lctx_1847_);
v___x_1849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1849_, 0, v_env_1844_);
lean_ctor_set(v___x_1849_, 1, v_mctx_1846_);
lean_ctor_set(v___x_1849_, 2, v_lctx_1847_);
lean_ctor_set(v___x_1849_, 3, v_options_1848_);
v___x_1850_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_msgData_1837_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1859_; double v___x_1860_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_float_of_nat(v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1864_, lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_ref_1871_; lean_object* v___x_1872_; lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1917_; 
v_ref_1871_ = lean_ctor_get(v___y_1868_, 5);
v___x_1872_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1917_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1917_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v_traceState_1878_; lean_object* v_env_1879_; lean_object* v_nextMacroScope_1880_; lean_object* v_ngen_1881_; lean_object* v_auxDeclNGen_1882_; lean_object* v_cache_1883_; lean_object* v_messages_1884_; lean_object* v_infoState_1885_; lean_object* v_snapshotTasks_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1916_; 
v___x_1877_ = lean_st_ref_take(v___y_1869_);
v_traceState_1878_ = lean_ctor_get(v___x_1877_, 4);
v_env_1879_ = lean_ctor_get(v___x_1877_, 0);
v_nextMacroScope_1880_ = lean_ctor_get(v___x_1877_, 1);
v_ngen_1881_ = lean_ctor_get(v___x_1877_, 2);
v_auxDeclNGen_1882_ = lean_ctor_get(v___x_1877_, 3);
v_cache_1883_ = lean_ctor_get(v___x_1877_, 5);
v_messages_1884_ = lean_ctor_get(v___x_1877_, 6);
v_infoState_1885_ = lean_ctor_get(v___x_1877_, 7);
v_snapshotTasks_1886_ = lean_ctor_get(v___x_1877_, 8);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1888_ = v___x_1877_;
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snapshotTasks_1886_);
lean_inc(v_infoState_1885_);
lean_inc(v_messages_1884_);
lean_inc(v_cache_1883_);
lean_inc(v_traceState_1878_);
lean_inc(v_auxDeclNGen_1882_);
lean_inc(v_ngen_1881_);
lean_inc(v_nextMacroScope_1880_);
lean_inc(v_env_1879_);
lean_dec(v___x_1877_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
uint64_t v_tid_1890_; lean_object* v_traces_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1915_; 
v_tid_1890_ = lean_ctor_get_uint64(v_traceState_1878_, sizeof(void*)*1);
v_traces_1891_ = lean_ctor_get(v_traceState_1878_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_traceState_1878_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1893_ = v_traceState_1878_;
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_traces_1891_);
lean_dec(v_traceState_1878_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; double v___x_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1897_ = 0;
v___x_1898_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1899_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1899_, 0, v_cls_1864_);
lean_ctor_set(v___x_1899_, 1, v___x_1895_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
lean_ctor_set_float(v___x_1899_, sizeof(void*)*3, v___x_1896_);
lean_ctor_set_float(v___x_1899_, sizeof(void*)*3 + 8, v___x_1896_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*3 + 16, v___x_1897_);
v___x_1900_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1901_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v_a_1873_);
lean_ctor_set(v___x_1901_, 2, v___x_1900_);
lean_inc(v_ref_1871_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_ref_1871_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_PersistentArray_push___redArg(v_traces_1891_, v___x_1902_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1903_);
v___x_1905_ = v___x_1893_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1903_);
lean_ctor_set_uint64(v_reuseFailAlloc_1914_, sizeof(void*)*1, v_tid_1890_);
v___x_1905_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 4, v___x_1905_);
v___x_1907_ = v___x_1888_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_env_1879_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_nextMacroScope_1880_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_ngen_1881_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_auxDeclNGen_1882_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_cache_1883_);
lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_messages_1884_);
lean_ctor_set(v_reuseFailAlloc_1913_, 7, v_infoState_1885_);
lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_snapshotTasks_1886_);
v___x_1907_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1908_ = lean_st_ref_set(v___y_1869_, v___x_1907_);
v___x_1909_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1909_);
v___x_1911_ = v___x_1875_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1918_, v_msg_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__1));
v___x_1931_ = l_Lean_Name_append(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__3));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__5));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7(void){
_start:
{
uint8_t v___x_1938_; uint64_t v___x_1939_; 
v___x_1938_ = 1;
v___x_1939_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__8));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__10));
v___x_1945_ = l_Lean_stringToMessageData(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_e_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
if (lean_obj_tag(v_e_1946_) == 11)
{
lean_object* v_typeName_1958_; lean_object* v_idx_1959_; lean_object* v_struct_1960_; lean_object* v___x_1961_; lean_object* v_env_1962_; lean_object* v___x_1963_; 
v_typeName_1958_ = lean_ctor_get(v_e_1946_, 0);
v_idx_1959_ = lean_ctor_get(v_e_1946_, 1);
v_struct_1960_ = lean_ctor_get(v_e_1946_, 2);
v___x_1961_ = lean_st_ref_get(v___y_1950_);
v_env_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc_ref(v_env_1962_);
lean_dec(v___x_1961_);
lean_inc(v_typeName_1958_);
v___x_1963_ = l_Lean_getStructureInfo_x3f(v_env_1962_, v_typeName_1958_);
if (lean_obj_tag(v___x_1963_) == 1)
{
lean_object* v_val_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2063_; 
v_val_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_2063_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_val_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2063_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_fieldNames_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_fieldNames_1968_ = lean_ctor_get(v_val_1964_, 1);
lean_inc_ref(v_fieldNames_1968_);
lean_dec(v_val_1964_);
v___x_1969_ = lean_array_get_size(v_fieldNames_1968_);
v___x_1970_ = lean_nat_dec_lt(v_idx_1959_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v_options_1971_; uint8_t v_hasTrace_1972_; 
lean_dec_ref(v_fieldNames_1968_);
v_options_1971_ = lean_ctor_get(v___y_1949_, 2);
v_hasTrace_1972_ = lean_ctor_get_uint8(v_options_1971_, sizeof(void*)*1);
if (v_hasTrace_1972_ == 0)
{
lean_del_object(v___x_1966_);
goto v___jp_1952_;
}
else
{
lean_object* v_inheritedTraceOptions_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_inheritedTraceOptions_1973_ = lean_ctor_get(v___y_1949_, 13);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1975_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_1976_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1973_, v_options_1971_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_del_object(v___x_1966_);
goto v___jp_1952_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4);
lean_inc(v_idx_1959_);
v___x_1978_ = l_Nat_reprFast(v_idx_1959_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 3);
lean_ctor_set(v___x_1966_, 0, v___x_1978_);
v___x_1980_ = v___x_1966_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1981_ = l_Lean_MessageData_ofFormat(v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1977_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
lean_inc_ref(v_e_1946_);
v___x_1985_ = l_Lean_indentExpr(v_e_1946_);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1974_, v___x_1986_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_dec_ref_known(v___x_1987_, 1);
goto v___jp_1952_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref_known(v_e_1946_, 3);
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1997_; uint8_t v_foApprox_1998_; uint8_t v_ctxApprox_1999_; uint8_t v_quasiPatternApprox_2000_; uint8_t v_constApprox_2001_; uint8_t v_isDefEqStuckEx_2002_; uint8_t v_unificationHints_2003_; uint8_t v_proofIrrelevance_2004_; uint8_t v_assignSyntheticOpaque_2005_; uint8_t v_offsetCnstrs_2006_; uint8_t v_etaStruct_2007_; uint8_t v_univApprox_2008_; uint8_t v_iota_2009_; uint8_t v_beta_2010_; uint8_t v_proj_2011_; uint8_t v_zeta_2012_; uint8_t v_zetaDelta_2013_; uint8_t v_zetaUnused_2014_; uint8_t v_zetaHave_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2062_; 
lean_inc_ref(v_struct_1960_);
lean_inc(v_idx_1959_);
lean_dec_ref_known(v_e_1946_, 3);
v___x_1997_ = l_Lean_Meta_Context_config(v___y_1947_);
v_foApprox_1998_ = lean_ctor_get_uint8(v___x_1997_, 0);
v_ctxApprox_1999_ = lean_ctor_get_uint8(v___x_1997_, 1);
v_quasiPatternApprox_2000_ = lean_ctor_get_uint8(v___x_1997_, 2);
v_constApprox_2001_ = lean_ctor_get_uint8(v___x_1997_, 3);
v_isDefEqStuckEx_2002_ = lean_ctor_get_uint8(v___x_1997_, 4);
v_unificationHints_2003_ = lean_ctor_get_uint8(v___x_1997_, 5);
v_proofIrrelevance_2004_ = lean_ctor_get_uint8(v___x_1997_, 6);
v_assignSyntheticOpaque_2005_ = lean_ctor_get_uint8(v___x_1997_, 7);
v_offsetCnstrs_2006_ = lean_ctor_get_uint8(v___x_1997_, 8);
v_etaStruct_2007_ = lean_ctor_get_uint8(v___x_1997_, 10);
v_univApprox_2008_ = lean_ctor_get_uint8(v___x_1997_, 11);
v_iota_2009_ = lean_ctor_get_uint8(v___x_1997_, 12);
v_beta_2010_ = lean_ctor_get_uint8(v___x_1997_, 13);
v_proj_2011_ = lean_ctor_get_uint8(v___x_1997_, 14);
v_zeta_2012_ = lean_ctor_get_uint8(v___x_1997_, 15);
v_zetaDelta_2013_ = lean_ctor_get_uint8(v___x_1997_, 16);
v_zetaUnused_2014_ = lean_ctor_get_uint8(v___x_1997_, 17);
v_zetaHave_2015_ = lean_ctor_get_uint8(v___x_1997_, 18);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2017_ = v___x_1997_;
v_isShared_2018_ = v_isSharedCheck_2062_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_1997_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2062_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
uint8_t v_trackZetaDelta_2019_; lean_object* v_zetaDeltaSet_2020_; lean_object* v_lctx_2021_; lean_object* v_localInstances_2022_; lean_object* v_defEqCtx_x3f_2023_; lean_object* v_synthPendingDepth_2024_; lean_object* v_canUnfold_x3f_2025_; uint8_t v_univApprox_2026_; uint8_t v_inTypeClassResolution_2027_; uint8_t v_cacheInferType_2028_; uint8_t v___x_2029_; lean_object* v_config_2031_; 
v_trackZetaDelta_2019_ = lean_ctor_get_uint8(v___y_1947_, sizeof(void*)*7);
v_zetaDeltaSet_2020_ = lean_ctor_get(v___y_1947_, 1);
v_lctx_2021_ = lean_ctor_get(v___y_1947_, 2);
v_localInstances_2022_ = lean_ctor_get(v___y_1947_, 3);
v_defEqCtx_x3f_2023_ = lean_ctor_get(v___y_1947_, 4);
v_synthPendingDepth_2024_ = lean_ctor_get(v___y_1947_, 5);
v_canUnfold_x3f_2025_ = lean_ctor_get(v___y_1947_, 6);
v_univApprox_2026_ = lean_ctor_get_uint8(v___y_1947_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2027_ = lean_ctor_get_uint8(v___y_1947_, sizeof(void*)*7 + 2);
v_cacheInferType_2028_ = lean_ctor_get_uint8(v___y_1947_, sizeof(void*)*7 + 3);
v___x_2029_ = 1;
if (v_isShared_2018_ == 0)
{
v_config_2031_ = v___x_2017_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 0, v_foApprox_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 1, v_ctxApprox_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 2, v_quasiPatternApprox_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 3, v_constApprox_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 4, v_isDefEqStuckEx_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 5, v_unificationHints_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 6, v_proofIrrelevance_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 7, v_assignSyntheticOpaque_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 8, v_offsetCnstrs_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 10, v_etaStruct_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 11, v_univApprox_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 12, v_iota_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 13, v_beta_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 14, v_proj_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 15, v_zeta_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 16, v_zetaDelta_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 17, v_zetaUnused_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, 18, v_zetaHave_2015_);
v_config_2031_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
uint64_t v___x_2032_; uint64_t v___x_2033_; uint64_t v___x_2034_; lean_object* v___x_2035_; uint64_t v___x_2036_; uint64_t v___x_2037_; uint64_t v_key_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_ctor_set_uint8(v_config_2031_, 9, v___x_2029_);
v___x_2032_ = l_Lean_Meta_Context_configKey(v___y_1947_);
v___x_2033_ = 3ULL;
v___x_2034_ = lean_uint64_shift_right(v___x_2032_, v___x_2033_);
v___x_2035_ = lean_array_fget(v_fieldNames_1968_, v_idx_1959_);
lean_dec(v_idx_1959_);
lean_dec_ref(v_fieldNames_1968_);
v___x_2036_ = lean_uint64_shift_left(v___x_2034_, v___x_2033_);
v___x_2037_ = lean_uint64_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__7, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7);
v_key_2038_ = lean_uint64_lor(v___x_2036_, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2039_, 0, v_config_2031_);
lean_ctor_set_uint64(v___x_2039_, sizeof(void*)*1, v_key_2038_);
lean_inc(v_canUnfold_x3f_2025_);
lean_inc(v_synthPendingDepth_2024_);
lean_inc(v_defEqCtx_x3f_2023_);
lean_inc_ref(v_localInstances_2022_);
lean_inc_ref(v_lctx_2021_);
lean_inc(v_zetaDeltaSet_2020_);
v___x_2040_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v_zetaDeltaSet_2020_);
lean_ctor_set(v___x_2040_, 2, v_lctx_2021_);
lean_ctor_set(v___x_2040_, 3, v_localInstances_2022_);
lean_ctor_set(v___x_2040_, 4, v_defEqCtx_x3f_2023_);
lean_ctor_set(v___x_2040_, 5, v_synthPendingDepth_2024_);
lean_ctor_set(v___x_2040_, 6, v_canUnfold_x3f_2025_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*7, v_trackZetaDelta_2019_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*7 + 1, v_univApprox_2026_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2027_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*7 + 3, v_cacheInferType_2028_);
v___x_2041_ = l_Lean_Meta_mkProjection(v_struct_1960_, v___x_2035_, v___x_2040_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec_ref_known(v___x_2040_, 7);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2052_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2052_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2052_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_a_2042_);
v___x_2047_ = v___x_1966_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2047_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_del_object(v___x_1966_);
v_a_2053_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2041_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2041_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
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
lean_object* v_options_2064_; uint8_t v_hasTrace_2065_; 
lean_dec(v___x_1963_);
v_options_2064_ = lean_ctor_get(v___y_1949_, 2);
v_hasTrace_2065_ = lean_ctor_get_uint8(v_options_2064_, sizeof(void*)*1);
if (v_hasTrace_2065_ == 0)
{
goto v___jp_1955_;
}
else
{
lean_object* v_inheritedTraceOptions_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_inheritedTraceOptions_2066_ = lean_ctor_get(v___y_1949_, 13);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2068_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_2069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2066_, v_options_2064_, v___x_2068_);
if (v___x_2069_ == 0)
{
goto v___jp_1955_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2070_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__9, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9);
lean_inc(v_typeName_1958_);
v___x_2071_ = l_Lean_MessageData_ofName(v_typeName_1958_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__11, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__11);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
lean_inc_ref(v_e_1946_);
v___x_2075_ = l_Lean_indentExpr(v_e_1946_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2067_, v___x_2076_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_dec_ref_known(v___x_2077_, 1);
goto v___jp_1955_;
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref_known(v_e_1946_, 3);
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_e_1946_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
v___jp_1952_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_e_1946_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
v___jp_1955_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_e_1946_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_e_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_e_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_x_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_x_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v_x_2103_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___f_2119_; lean_object* v___x_2120_; 
v___f_2119_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2120_ = lean_find_expr(v___f_2119_, v_e_2113_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_e_2113_);
return v___x_2121_;
}
else
{
lean_object* v_post_2122_; lean_object* v___f_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref_known(v___x_2120_, 1);
v_post_2122_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v___f_2123_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2124_ = 0;
v___x_2125_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2113_, v___f_2123_, v_post_2122_, v___x_2124_, v___x_2124_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Meta_Sym_foldProjs(v_e_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
return v_res_2132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = lean_box(0);
v___x_2137_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2138_ = l_Lean_mkConst(v___x_2137_, v___x_2136_);
return v___x_2138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2144_ = l_Lean_mkConst(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2152_ = l_Lean_mkConst(v___x_2151_, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2159_ = l_Lean_mkConst(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = l_Lean_mkNatLit(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2169_ = l_Lean_mkConst(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2173_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2172_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
v_a_2175_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2173_, 2);
v___x_2176_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2177_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2176_, v_a_2170_, v_a_2175_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
v_a_2179_ = lean_ctor_get(v___x_2177_, 1);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2177_, 2);
v___x_2180_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2181_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2180_, v_a_2170_, v_a_2179_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
v_a_2183_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2181_, 2);
v___x_2184_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2185_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2184_, v_a_2170_, v_a_2183_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v_a_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
v_a_2187_ = lean_ctor_get(v___x_2185_, 1);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2185_, 2);
v___x_2188_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2189_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2188_, v_a_2170_, v_a_2187_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
v_a_2191_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2189_, 2);
v___x_2192_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2193_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2192_, v_a_2170_, v_a_2191_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v_a_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
v_a_2195_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2193_, 2);
v___x_2196_ = l_Lean_Int_mkType;
v___x_2197_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2196_, v_a_2170_, v_a_2195_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2207_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_a_2199_ = lean_ctor_get(v___x_2197_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2201_ = v___x_2197_;
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2178_);
lean_ctor_set(v___x_2203_, 1, v_a_2174_);
lean_ctor_set(v___x_2203_, 2, v_a_2190_);
lean_ctor_set(v___x_2203_, 3, v_a_2186_);
lean_ctor_set(v___x_2203_, 4, v_a_2182_);
lean_ctor_set(v___x_2203_, 5, v_a_2194_);
lean_ctor_set(v___x_2203_, 6, v_a_2198_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_a_2199_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2194_);
lean_dec(v_a_2190_);
lean_dec(v_a_2186_);
lean_dec(v_a_2182_);
lean_dec(v_a_2178_);
lean_dec(v_a_2174_);
v_a_2208_ = lean_ctor_get(v___x_2197_, 0);
v_a_2209_ = lean_ctor_get(v___x_2197_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2197_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_inc(v_a_2208_);
lean_dec(v___x_2197_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2208_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_a_2190_);
lean_dec(v_a_2186_);
lean_dec(v_a_2182_);
lean_dec(v_a_2178_);
lean_dec(v_a_2174_);
v_a_2217_ = lean_ctor_get(v___x_2193_, 0);
v_a_2218_ = lean_ctor_get(v___x_2193_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2193_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_inc(v_a_2217_);
lean_dec(v___x_2193_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2217_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_2186_);
lean_dec(v_a_2182_);
lean_dec(v_a_2178_);
lean_dec(v_a_2174_);
v_a_2226_ = lean_ctor_get(v___x_2189_, 0);
v_a_2227_ = lean_ctor_get(v___x_2189_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2189_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_inc(v_a_2226_);
lean_dec(v___x_2189_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2226_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2182_);
lean_dec(v_a_2178_);
lean_dec(v_a_2174_);
v_a_2235_ = lean_ctor_get(v___x_2185_, 0);
v_a_2236_ = lean_ctor_get(v___x_2185_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2185_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_inc(v_a_2235_);
lean_dec(v___x_2185_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2235_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_a_2178_);
lean_dec(v_a_2174_);
v_a_2244_ = lean_ctor_get(v___x_2181_, 0);
v_a_2245_ = lean_ctor_get(v___x_2181_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2181_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_inc(v_a_2244_);
lean_dec(v___x_2181_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2244_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2174_);
v_a_2253_ = lean_ctor_get(v___x_2177_, 0);
v_a_2254_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2177_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_inc(v_a_2253_);
lean_dec(v___x_2177_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2253_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_a_2262_ = lean_ctor_get(v___x_2173_, 0);
v_a_2263_ = lean_ctor_get(v___x_2173_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2173_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_inc(v_a_2262_);
lean_dec(v___x_2173_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2262_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2271_, v_a_2272_);
lean_dec_ref(v_a_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2274_, lean_object* v_opt_2275_){
_start:
{
lean_object* v_name_2276_; lean_object* v_defValue_2277_; lean_object* v_map_2278_; lean_object* v___x_2279_; 
v_name_2276_ = lean_ctor_get(v_opt_2275_, 0);
v_defValue_2277_ = lean_ctor_get(v_opt_2275_, 1);
v_map_2278_ = lean_ctor_get(v_opts_2274_, 0);
v___x_2279_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2278_, v_name_2276_);
if (lean_obj_tag(v___x_2279_) == 0)
{
uint8_t v___x_2280_; 
v___x_2280_ = lean_unbox(v_defValue_2277_);
return v___x_2280_;
}
else
{
lean_object* v_val_2281_; 
v_val_2281_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___x_2279_, 1);
if (lean_obj_tag(v_val_2281_) == 1)
{
uint8_t v_v_2282_; 
v_v_2282_ = lean_ctor_get_uint8(v_val_2281_, 0);
lean_dec_ref_known(v_val_2281_, 0);
return v_v_2282_;
}
else
{
uint8_t v___x_2283_; 
lean_dec(v_val_2281_);
v___x_2283_ = lean_unbox(v_defValue_2277_);
return v___x_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2284_, lean_object* v_opt_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2284_, v_opt_2285_);
lean_dec_ref(v_opt_2285_);
lean_dec_ref(v_opts_2284_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___f_2300_; lean_object* v___x_2122__overap_2301_; lean_object* v___x_2302_; 
v___f_2300_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2122__overap_2301_ = lean_panic_fn_borrowed(v___f_2300_, v_msg_2294_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
v___x_2302_ = lean_apply_5(v___x_2122__overap_2301_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, lean_box(0));
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2309_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_box(0));
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2319_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_2320_ = lean_unsigned_to_nat(19u);
v___x_2321_ = lean_unsigned_to_nat(304u);
v___x_2322_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__5));
v___x_2323_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2324_ = l_mkPanicMessageWithDecl(v___x_2323_, v___x_2322_, v___x_2321_, v___x_2320_, v___x_2319_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_fst_2332_; lean_object* v_snd_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___x_2373_; lean_object* v_env_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = lean_st_ref_get(v_a_2329_);
v_env_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc_ref(v_env_2374_);
lean_dec(v___x_2373_);
v___x_2375_ = 0;
v___x_2376_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2376_, 0, v_env_2374_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*1, v___x_2375_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*1 + 1, v___x_2375_);
v___x_2377_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
v___x_2378_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2376_, v___x_2377_);
lean_dec_ref_known(v___x_2376_, 1);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v_a_2380_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
v_a_2380_ = lean_ctor_get(v___x_2378_, 1);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2378_, 2);
v_fst_2332_ = v_a_2379_;
v_snd_2333_ = v_a_2380_;
v___y_2334_ = v_a_2326_;
v___y_2335_ = v_a_2327_;
v___y_2336_ = v_a_2328_;
v___y_2337_ = v_a_2329_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref_known(v___x_2378_, 2);
v___x_2381_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__7, &l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7);
v___x_2382_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2381_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v_fst_2384_; lean_object* v_snd_2385_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v_fst_2384_ = lean_ctor_get(v_a_2383_, 0);
lean_inc(v_fst_2384_);
v_snd_2385_ = lean_ctor_get(v_a_2383_, 1);
lean_inc(v_snd_2385_);
lean_dec(v_a_2383_);
v_fst_2332_ = v_fst_2384_;
v_snd_2333_ = v_snd_2385_;
v___y_2334_ = v_a_2326_;
v___y_2335_ = v_a_2327_;
v___y_2336_ = v_a_2328_;
v___y_2337_ = v_a_2329_;
goto v___jp_2331_;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v_x_2325_);
v_a_2386_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2382_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
v___jp_2331_:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v_options_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v_options_2340_ = lean_ctor_get(v___y_2336_, 2);
v___x_2341_ = l_Lean_Meta_Sym_sym_debug;
v___x_2342_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_options_2340_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2344_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_2347_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v___x_2347_, 0, v_snd_2333_);
lean_ctor_set(v___x_2347_, 1, v___x_2344_);
lean_ctor_set(v___x_2347_, 2, v___x_2344_);
lean_ctor_set(v___x_2347_, 3, v___x_2344_);
lean_ctor_set(v___x_2347_, 4, v___x_2344_);
lean_ctor_set(v___x_2347_, 5, v___x_2344_);
lean_ctor_set(v___x_2347_, 6, v___x_2344_);
lean_ctor_set(v___x_2347_, 7, v_a_2339_);
lean_ctor_set(v___x_2347_, 8, v___x_2345_);
lean_ctor_set(v___x_2347_, 9, v___x_2346_);
lean_ctor_set(v___x_2347_, 10, v___x_2344_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*11, v___x_2342_);
v___x_2348_ = lean_st_mk_ref(v___x_2347_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_fst_2332_);
lean_ctor_set(v___x_2349_, 1, v___x_2343_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v___x_2348_);
v___x_2350_ = lean_apply_7(v_x_2325_, v___x_2349_, v___x_2348_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, lean_box(0));
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2359_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2355_ = lean_st_ref_get(v___x_2348_);
lean_dec(v___x_2348_);
lean_dec(v___x_2355_);
if (v_isShared_2354_ == 0)
{
v___x_2357_ = v___x_2353_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2351_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_dec(v___x_2348_);
return v___x_2350_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_snd_2333_);
lean_dec_ref(v_fst_2332_);
lean_dec_ref(v_x_2325_);
v_a_2360_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2362_ = v___x_2338_;
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2338_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_ref_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v_ref_2364_ = lean_ctor_get(v___y_2336_, 5);
v___x_2365_ = lean_io_error_to_string(v_a_2360_);
v___x_2366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = l_Lean_MessageData_ofFormat(v___x_2366_);
lean_inc(v_ref_2364_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_ref_2364_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2368_);
v___x_2370_ = v___x_2362_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2401_, lean_object* v_x_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_x_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2409_, v_x_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2417_){
_start:
{
lean_object* v_sharedExprs_2419_; lean_object* v___x_2420_; 
v_sharedExprs_2419_ = lean_ctor_get(v_a_2417_, 0);
lean_inc_ref(v_sharedExprs_2419_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_sharedExprs_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2421_);
lean_dec_ref(v_a_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2424_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v___x_2442_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2440_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_trueExpr_2447_; lean_object* v___x_2449_; 
v_trueExpr_2447_ = lean_ctor_get(v_a_2443_, 0);
lean_inc_ref(v_trueExpr_2447_);
lean_dec(v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v_trueExpr_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_trueExpr_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2452_);
lean_dec_ref(v_a_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2455_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2472_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2484_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2484_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2484_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2479_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2471_, v_a_2475_);
lean_dec(v_a_2475_);
v___x_2480_ = lean_box(v___x_2479_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2480_);
v___x_2482_ = v___x_2477_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
v_a_2485_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2474_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2474_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2493_, v_a_2494_);
lean_dec_ref(v_a_2494_);
lean_dec_ref(v_e_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2497_, v_a_2498_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec_ref(v_e_2506_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2517_; lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
v___x_2517_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2515_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_falseExpr_2522_; lean_object* v___x_2524_; 
v_falseExpr_2522_ = lean_ctor_get(v_a_2518_, 1);
lean_inc_ref(v_falseExpr_2522_);
lean_dec(v_a_2518_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v_falseExpr_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_falseExpr_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2527_);
lean_dec_ref(v_a_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2530_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2547_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2559_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2559_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2559_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2554_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2546_, v_a_2550_);
lean_dec(v_a_2550_);
v___x_2555_ = lean_box(v___x_2554_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2555_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2549_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2549_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2568_, v_a_2569_);
lean_dec_ref(v_a_2569_);
lean_dec_ref(v_e_2568_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2572_, v_a_2573_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec_ref(v_e_2581_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2601_; 
v___x_2592_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2590_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_btrueExpr_2597_; lean_object* v___x_2599_; 
v_btrueExpr_2597_ = lean_ctor_get(v_a_2593_, 3);
lean_inc_ref(v_btrueExpr_2597_);
lean_dec(v_a_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_btrueExpr_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_btrueExpr_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2602_);
lean_dec_ref(v_a_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2605_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2622_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2634_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2634_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2634_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2629_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2621_, v_a_2625_);
lean_dec(v_a_2625_);
v___x_2630_ = lean_box(v___x_2629_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2630_);
v___x_2632_ = v___x_2627_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_a_2635_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2624_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2624_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2643_, v_a_2644_);
lean_dec_ref(v_a_2644_);
lean_dec_ref(v_e_2643_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2647_, v_a_2648_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec_ref(v_e_2656_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2676_; 
v___x_2667_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2665_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_bfalseExpr_2672_; lean_object* v___x_2674_; 
v_bfalseExpr_2672_ = lean_ctor_get(v_a_2668_, 4);
lean_inc_ref(v_bfalseExpr_2672_);
lean_dec(v_a_2668_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v_bfalseExpr_2672_);
v___x_2674_ = v___x_2670_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_bfalseExpr_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2677_);
lean_dec_ref(v_a_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2680_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2697_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2709_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2709_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2709_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2704_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2696_, v_a_2700_);
lean_dec(v_a_2700_);
v___x_2705_ = lean_box(v___x_2704_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2705_);
v___x_2707_ = v___x_2702_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_a_2710_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2699_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2699_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2718_, v_a_2719_);
lean_dec_ref(v_a_2719_);
lean_dec_ref(v_e_2718_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2722_, v_a_2723_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec_ref(v_e_2731_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v___x_2742_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2740_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_natZExpr_2747_; lean_object* v___x_2749_; 
v_natZExpr_2747_ = lean_ctor_get(v_a_2743_, 2);
lean_inc_ref(v_natZExpr_2747_);
lean_dec(v_a_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_natZExpr_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_natZExpr_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2752_);
lean_dec_ref(v_a_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2755_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2782_; 
v___x_2773_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2771_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_ordEqExpr_2778_; lean_object* v___x_2780_; 
v_ordEqExpr_2778_ = lean_ctor_get(v_a_2774_, 5);
lean_inc_ref(v_ordEqExpr_2778_);
lean_dec(v_a_2774_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v_ordEqExpr_2778_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_ordEqExpr_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2783_);
lean_dec_ref(v_a_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2786_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2802_){
_start:
{
lean_object* v___x_2804_; lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2813_; 
v___x_2804_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2802_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2813_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2813_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_intExpr_2809_; lean_object* v___x_2811_; 
v_intExpr_2809_ = lean_ctor_get(v_a_2805_, 6);
lean_inc_ref(v_intExpr_2809_);
lean_dec(v_a_2805_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v_intExpr_2809_);
v___x_2811_ = v___x_2807_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_intExpr_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2814_);
lean_dec_ref(v_a_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2817_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Meta_Sym_getIntExpr(v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2833_, lean_object* v_ctx_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v___x_2837_; lean_object* v_share_2838_; lean_object* v_maxFVar_2839_; lean_object* v_proofInstInfo_2840_; lean_object* v_inferType_2841_; lean_object* v_getLevel_2842_; lean_object* v_congrInfo_2843_; lean_object* v_defEqI_2844_; lean_object* v_extensions_2845_; lean_object* v_issues_2846_; lean_object* v_canon_2847_; lean_object* v_instanceOverrides_2848_; uint8_t v_debug_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2909_; 
v___x_2837_ = lean_st_ref_take(v_a_2835_);
v_share_2838_ = lean_ctor_get(v___x_2837_, 0);
v_maxFVar_2839_ = lean_ctor_get(v___x_2837_, 1);
v_proofInstInfo_2840_ = lean_ctor_get(v___x_2837_, 2);
v_inferType_2841_ = lean_ctor_get(v___x_2837_, 3);
v_getLevel_2842_ = lean_ctor_get(v___x_2837_, 4);
v_congrInfo_2843_ = lean_ctor_get(v___x_2837_, 5);
v_defEqI_2844_ = lean_ctor_get(v___x_2837_, 6);
v_extensions_2845_ = lean_ctor_get(v___x_2837_, 7);
v_issues_2846_ = lean_ctor_get(v___x_2837_, 8);
v_canon_2847_ = lean_ctor_get(v___x_2837_, 9);
v_instanceOverrides_2848_ = lean_ctor_get(v___x_2837_, 10);
v_debug_2849_ = lean_ctor_get_uint8(v___x_2837_, sizeof(void*)*11);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2851_ = v___x_2837_;
v_isShared_2852_ = v_isSharedCheck_2909_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_instanceOverrides_2848_);
lean_inc(v_canon_2847_);
lean_inc(v_issues_2846_);
lean_inc(v_extensions_2845_);
lean_inc(v_defEqI_2844_);
lean_inc(v_congrInfo_2843_);
lean_inc(v_getLevel_2842_);
lean_inc(v_inferType_2841_);
lean_inc(v_proofInstInfo_2840_);
lean_inc(v_maxFVar_2839_);
lean_inc(v_share_2838_);
lean_dec(v___x_2837_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2909_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_maxFVar_2839_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_proofInstInfo_2840_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v_inferType_2841_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v_getLevel_2842_);
lean_ctor_set(v_reuseFailAlloc_2908_, 5, v_congrInfo_2843_);
lean_ctor_set(v_reuseFailAlloc_2908_, 6, v_defEqI_2844_);
lean_ctor_set(v_reuseFailAlloc_2908_, 7, v_extensions_2845_);
lean_ctor_set(v_reuseFailAlloc_2908_, 8, v_issues_2846_);
lean_ctor_set(v_reuseFailAlloc_2908_, 9, v_canon_2847_);
lean_ctor_set(v_reuseFailAlloc_2908_, 10, v_instanceOverrides_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, sizeof(void*)*11, v_debug_2849_);
v___x_2855_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_st_ref_set(v_a_2835_, v___x_2855_);
v___x_2857_ = lean_apply_2(v_k_2833_, v_ctx_2834_, v_share_2838_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_a_2859_; lean_object* v___x_2860_; lean_object* v_maxFVar_2861_; lean_object* v_proofInstInfo_2862_; lean_object* v_inferType_2863_; lean_object* v_getLevel_2864_; lean_object* v_congrInfo_2865_; lean_object* v_defEqI_2866_; lean_object* v_extensions_2867_; lean_object* v_issues_2868_; lean_object* v_canon_2869_; lean_object* v_instanceOverrides_2870_; uint8_t v_debug_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2881_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
v_a_2859_ = lean_ctor_get(v___x_2857_, 1);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2857_, 2);
v___x_2860_ = lean_st_ref_take(v_a_2835_);
v_maxFVar_2861_ = lean_ctor_get(v___x_2860_, 1);
v_proofInstInfo_2862_ = lean_ctor_get(v___x_2860_, 2);
v_inferType_2863_ = lean_ctor_get(v___x_2860_, 3);
v_getLevel_2864_ = lean_ctor_get(v___x_2860_, 4);
v_congrInfo_2865_ = lean_ctor_get(v___x_2860_, 5);
v_defEqI_2866_ = lean_ctor_get(v___x_2860_, 6);
v_extensions_2867_ = lean_ctor_get(v___x_2860_, 7);
v_issues_2868_ = lean_ctor_get(v___x_2860_, 8);
v_canon_2869_ = lean_ctor_get(v___x_2860_, 9);
v_instanceOverrides_2870_ = lean_ctor_get(v___x_2860_, 10);
v_debug_2871_ = lean_ctor_get_uint8(v___x_2860_, sizeof(void*)*11);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2860_, 0);
lean_dec(v_unused_2882_);
v___x_2873_ = v___x_2860_;
v_isShared_2874_ = v_isSharedCheck_2881_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_instanceOverrides_2870_);
lean_inc(v_canon_2869_);
lean_inc(v_issues_2868_);
lean_inc(v_extensions_2867_);
lean_inc(v_defEqI_2866_);
lean_inc(v_congrInfo_2865_);
lean_inc(v_getLevel_2864_);
lean_inc(v_inferType_2863_);
lean_inc(v_proofInstInfo_2862_);
lean_inc(v_maxFVar_2861_);
lean_dec(v___x_2860_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2881_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v_a_2859_);
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2859_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_maxFVar_2861_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_proofInstInfo_2862_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_inferType_2863_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_getLevel_2864_);
lean_ctor_set(v_reuseFailAlloc_2880_, 5, v_congrInfo_2865_);
lean_ctor_set(v_reuseFailAlloc_2880_, 6, v_defEqI_2866_);
lean_ctor_set(v_reuseFailAlloc_2880_, 7, v_extensions_2867_);
lean_ctor_set(v_reuseFailAlloc_2880_, 8, v_issues_2868_);
lean_ctor_set(v_reuseFailAlloc_2880_, 9, v_canon_2869_);
lean_ctor_set(v_reuseFailAlloc_2880_, 10, v_instanceOverrides_2870_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*11, v_debug_2871_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_st_ref_set(v_a_2835_, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_a_2858_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v_maxFVar_2886_; lean_object* v_proofInstInfo_2887_; lean_object* v_inferType_2888_; lean_object* v_getLevel_2889_; lean_object* v_congrInfo_2890_; lean_object* v_defEqI_2891_; lean_object* v_extensions_2892_; lean_object* v_issues_2893_; lean_object* v_canon_2894_; lean_object* v_instanceOverrides_2895_; uint8_t v_debug_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2906_; 
v_a_2883_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2883_);
v_a_2884_ = lean_ctor_get(v___x_2857_, 1);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2857_, 2);
v___x_2885_ = lean_st_ref_take(v_a_2835_);
v_maxFVar_2886_ = lean_ctor_get(v___x_2885_, 1);
v_proofInstInfo_2887_ = lean_ctor_get(v___x_2885_, 2);
v_inferType_2888_ = lean_ctor_get(v___x_2885_, 3);
v_getLevel_2889_ = lean_ctor_get(v___x_2885_, 4);
v_congrInfo_2890_ = lean_ctor_get(v___x_2885_, 5);
v_defEqI_2891_ = lean_ctor_get(v___x_2885_, 6);
v_extensions_2892_ = lean_ctor_get(v___x_2885_, 7);
v_issues_2893_ = lean_ctor_get(v___x_2885_, 8);
v_canon_2894_ = lean_ctor_get(v___x_2885_, 9);
v_instanceOverrides_2895_ = lean_ctor_get(v___x_2885_, 10);
v_debug_2896_ = lean_ctor_get_uint8(v___x_2885_, sizeof(void*)*11);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2907_);
v___x_2898_ = v___x_2885_;
v_isShared_2899_ = v_isSharedCheck_2906_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_instanceOverrides_2895_);
lean_inc(v_canon_2894_);
lean_inc(v_issues_2893_);
lean_inc(v_extensions_2892_);
lean_inc(v_defEqI_2891_);
lean_inc(v_congrInfo_2890_);
lean_inc(v_getLevel_2889_);
lean_inc(v_inferType_2888_);
lean_inc(v_proofInstInfo_2887_);
lean_inc(v_maxFVar_2886_);
lean_dec(v___x_2885_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2906_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_a_2884_);
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2884_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_maxFVar_2886_);
lean_ctor_set(v_reuseFailAlloc_2905_, 2, v_proofInstInfo_2887_);
lean_ctor_set(v_reuseFailAlloc_2905_, 3, v_inferType_2888_);
lean_ctor_set(v_reuseFailAlloc_2905_, 4, v_getLevel_2889_);
lean_ctor_set(v_reuseFailAlloc_2905_, 5, v_congrInfo_2890_);
lean_ctor_set(v_reuseFailAlloc_2905_, 6, v_defEqI_2891_);
lean_ctor_set(v_reuseFailAlloc_2905_, 7, v_extensions_2892_);
lean_ctor_set(v_reuseFailAlloc_2905_, 8, v_issues_2893_);
lean_ctor_set(v_reuseFailAlloc_2905_, 9, v_canon_2894_);
lean_ctor_set(v_reuseFailAlloc_2905_, 10, v_instanceOverrides_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2905_, sizeof(void*)*11, v_debug_2896_);
v___x_2901_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2902_ = lean_st_ref_set(v_a_2835_, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_a_2883_);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2910_, lean_object* v_ctx_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2910_, v_ctx_2911_, v_a_2912_);
lean_dec(v_a_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2915_, lean_object* v_k_2916_, lean_object* v_ctx_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2916_, v_ctx_2917_, v_a_2919_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_k_2927_, lean_object* v_ctx_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2926_, v_k_2927_, v_ctx_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2937_){
_start:
{
lean_object* v_config_2938_; lean_object* v_sharedExprs_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2956_; 
v_config_2938_ = lean_ctor_get(v_ctx_2937_, 1);
v_sharedExprs_2939_ = lean_ctor_get(v_ctx_2937_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_ctx_2937_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2941_ = v_ctx_2937_;
v_isShared_2942_ = v_isSharedCheck_2956_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_config_2938_);
lean_inc(v_sharedExprs_2939_);
lean_dec(v_ctx_2937_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2956_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
uint8_t v_verbose_2943_; uint8_t v_enforceUnfoldReducible_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2955_; 
v_verbose_2943_ = lean_ctor_get_uint8(v_config_2938_, 0);
v_enforceUnfoldReducible_2944_ = lean_ctor_get_uint8(v_config_2938_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_config_2938_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2946_ = v_config_2938_;
v_isShared_2947_ = v_isSharedCheck_2955_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_config_2938_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2955_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = 0;
if (v_isShared_2947_ == 0)
{
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2954_, 0, v_verbose_2943_);
lean_ctor_set_uint8(v_reuseFailAlloc_2954_, 1, v_enforceUnfoldReducible_2944_);
v___x_2950_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2952_; 
lean_ctor_set_uint8(v___x_2950_, 2, v___x_2948_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2950_);
v___x_2952_ = v___x_2941_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_sharedExprs_2939_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v___f_2960_; lean_object* v___x_2961_; 
v___f_2960_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2961_ = lean_apply_3(v_inst_2958_, lean_box(0), v___f_2960_, v_x_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2962_, lean_object* v_00_u03b1_2963_, lean_object* v_inst_2964_, lean_object* v_x_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2964_, v_x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2967_){
_start:
{
lean_object* v_config_2968_; lean_object* v_sharedExprs_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2985_; 
v_config_2968_ = lean_ctor_get(v_ctx_2967_, 1);
v_sharedExprs_2969_ = lean_ctor_get(v_ctx_2967_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_ctx_2967_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2971_ = v_ctx_2967_;
v_isShared_2972_ = v_isSharedCheck_2985_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_config_2968_);
lean_inc(v_sharedExprs_2969_);
lean_dec(v_ctx_2967_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2985_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
uint8_t v_verbose_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2984_; 
v_verbose_2973_ = lean_ctor_get_uint8(v_config_2968_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_config_2968_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2975_ = v_config_2968_;
v_isShared_2976_ = v_isSharedCheck_2984_;
goto v_resetjp_2974_;
}
else
{
lean_dec(v_config_2968_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2984_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
uint8_t v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = 0;
if (v_isShared_2976_ == 0)
{
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2983_, 0, v_verbose_2973_);
v___x_2979_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
lean_ctor_set_uint8(v___x_2979_, 1, v___x_2977_);
lean_ctor_set_uint8(v___x_2979_, 2, v___x_2977_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 1, v___x_2979_);
v___x_2981_ = v___x_2971_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_sharedExprs_2969_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_2987_, lean_object* v_x_2988_){
_start:
{
lean_object* v___f_2989_; lean_object* v___x_2990_; 
v___f_2989_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_2990_ = lean_apply_3(v_inst_2987_, lean_box(0), v___f_2989_, v_x_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_2991_, lean_object* v_00_u03b1_2992_, lean_object* v_inst_2993_, lean_object* v_x_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_2993_, v_x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v_config_3000_; lean_object* v_env_3001_; uint8_t v_enforceUnfoldReducible_3002_; uint8_t v_enforceFoldProjs_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_2999_ = lean_st_ref_get(v_a_2997_);
v_config_3000_ = lean_ctor_get(v_a_2996_, 1);
v_env_3001_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_env_3001_);
lean_dec(v___x_2999_);
v_enforceUnfoldReducible_3002_ = lean_ctor_get_uint8(v_config_3000_, 1);
v_enforceFoldProjs_3003_ = lean_ctor_get_uint8(v_config_3000_, 2);
v___x_3004_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3004_, 0, v_env_3001_);
lean_ctor_set_uint8(v___x_3004_, sizeof(void*)*1, v_enforceUnfoldReducible_3002_);
lean_ctor_set_uint8(v___x_3004_, sizeof(void*)*1 + 1, v_enforceFoldProjs_3003_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3006_, v_a_3007_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3010_, v_a_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_config_3033_; uint8_t v_enforceUnfoldReducible_3034_; uint8_t v_enforceFoldProjs_3035_; lean_object* v_e_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v_e_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; 
v_config_3033_ = lean_ctor_get(v_a_3027_, 1);
v_enforceUnfoldReducible_3034_ = lean_ctor_get_uint8(v_config_3033_, 1);
v_enforceFoldProjs_3035_ = lean_ctor_get_uint8(v_config_3033_, 2);
if (v_enforceUnfoldReducible_3034_ == 0)
{
v_e_3045_ = v_e_3026_;
v___y_3046_ = v_a_3028_;
v___y_3047_ = v_a_3029_;
v___y_3048_ = v_a_3030_;
v___y_3049_ = v_a_3031_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3026_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v_e_3045_ = v_a_3053_;
v___y_3046_ = v_a_3028_;
v___y_3047_ = v_a_3029_;
v___y_3048_ = v_a_3030_;
v___y_3049_ = v_a_3031_;
goto v___jp_3044_;
}
else
{
return v___x_3052_;
}
}
v___jp_3036_:
{
if (v_enforceUnfoldReducible_3034_ == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_e_3037_);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
return v___x_3043_;
}
}
v___jp_3044_:
{
if (v_enforceFoldProjs_3035_ == 0)
{
v_e_3037_ = v_e_3045_;
v___y_3038_ = v___y_3046_;
v___y_3039_ = v___y_3047_;
v___y_3040_ = v___y_3048_;
v___y_3041_ = v___y_3049_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Meta_Sym_foldProjs(v_e_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v_e_3037_ = v_a_3051_;
v___y_3038_ = v___y_3046_;
v___y_3039_ = v___y_3047_;
v___y_3040_ = v___y_3048_;
v___y_3041_ = v___y_3049_;
goto v___jp_3036_;
}
else
{
return v___x_3050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec_ref(v_a_3055_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3062_, v_a_3063_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
return v_res_3079_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_instMonadEIO(lean_box(0));
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_toApplicative_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3158_; 
v___x_3093_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3094_ = l_StateRefT_x27_instMonad___redArg(v___x_3093_);
v_toApplicative_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v___x_3094_, 1);
lean_dec(v_unused_3159_);
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3158_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_toApplicative_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3158_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_toFunctor_3099_; lean_object* v_toSeq_3100_; lean_object* v_toSeqLeft_3101_; lean_object* v_toSeqRight_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3156_; 
v_toFunctor_3099_ = lean_ctor_get(v_toApplicative_3095_, 0);
v_toSeq_3100_ = lean_ctor_get(v_toApplicative_3095_, 2);
v_toSeqLeft_3101_ = lean_ctor_get(v_toApplicative_3095_, 3);
v_toSeqRight_3102_ = lean_ctor_get(v_toApplicative_3095_, 4);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_toApplicative_3095_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v_toApplicative_3095_, 1);
lean_dec(v_unused_3157_);
v___x_3104_ = v_toApplicative_3095_;
v_isShared_3105_ = v_isSharedCheck_3156_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_toSeqRight_3102_);
lean_inc(v_toSeqLeft_3101_);
lean_inc(v_toSeq_3100_);
lean_inc(v_toFunctor_3099_);
lean_dec(v_toApplicative_3095_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3156_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___f_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v___f_3111_; lean_object* v___f_3112_; lean_object* v___f_3113_; lean_object* v___x_3115_; 
v___f_3106_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3107_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3099_);
v___f_3108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3108_, 0, v_toFunctor_3099_);
v___f_3109_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3109_, 0, v_toFunctor_3099_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___f_3108_);
lean_ctor_set(v___x_3110_, 1, v___f_3109_);
v___f_3111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3111_, 0, v_toSeqRight_3102_);
v___f_3112_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3112_, 0, v_toSeqLeft_3101_);
v___f_3113_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3113_, 0, v_toSeq_3100_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 4, v___f_3111_);
lean_ctor_set(v___x_3104_, 3, v___f_3112_);
lean_ctor_set(v___x_3104_, 2, v___f_3113_);
lean_ctor_set(v___x_3104_, 1, v___f_3106_);
lean_ctor_set(v___x_3104_, 0, v___x_3110_);
v___x_3115_ = v___x_3104_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___f_3106_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v___f_3113_);
lean_ctor_set(v_reuseFailAlloc_3155_, 3, v___f_3112_);
lean_ctor_set(v_reuseFailAlloc_3155_, 4, v___f_3111_);
v___x_3115_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3117_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___f_3107_);
lean_ctor_set(v___x_3097_, 0, v___x_3115_);
v___x_3117_ = v___x_3097_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___f_3107_);
v___x_3117_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v_toApplicative_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3152_; 
v___x_3118_ = l_StateRefT_x27_instMonad___redArg(v___x_3117_);
v_toApplicative_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v___x_3118_, 1);
lean_dec(v_unused_3153_);
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3152_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_toApplicative_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3152_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_toFunctor_3123_; lean_object* v_toSeq_3124_; lean_object* v_toSeqLeft_3125_; lean_object* v_toSeqRight_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3150_; 
v_toFunctor_3123_ = lean_ctor_get(v_toApplicative_3119_, 0);
v_toSeq_3124_ = lean_ctor_get(v_toApplicative_3119_, 2);
v_toSeqLeft_3125_ = lean_ctor_get(v_toApplicative_3119_, 3);
v_toSeqRight_3126_ = lean_ctor_get(v_toApplicative_3119_, 4);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_toApplicative_3119_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_toApplicative_3119_, 1);
lean_dec(v_unused_3151_);
v___x_3128_ = v_toApplicative_3119_;
v_isShared_3129_ = v_isSharedCheck_3150_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_toSeqRight_3126_);
lean_inc(v_toSeqLeft_3125_);
lean_inc(v_toSeq_3124_);
lean_inc(v_toFunctor_3123_);
lean_dec(v_toApplicative_3119_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3150_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___f_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___f_3136_; lean_object* v___f_3137_; lean_object* v___x_3139_; 
v___f_3130_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3131_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3123_);
v___f_3132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3132_, 0, v_toFunctor_3123_);
v___f_3133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3133_, 0, v_toFunctor_3123_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___f_3132_);
lean_ctor_set(v___x_3134_, 1, v___f_3133_);
v___f_3135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3135_, 0, v_toSeqRight_3126_);
v___f_3136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3136_, 0, v_toSeqLeft_3125_);
v___f_3137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3137_, 0, v_toSeq_3124_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 4, v___f_3135_);
lean_ctor_set(v___x_3128_, 3, v___f_3136_);
lean_ctor_set(v___x_3128_, 2, v___f_3137_);
lean_ctor_set(v___x_3128_, 1, v___f_3130_);
lean_ctor_set(v___x_3128_, 0, v___x_3134_);
v___x_3139_ = v___x_3128_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v___f_3130_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v___f_3137_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v___f_3136_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v___f_3135_);
v___x_3139_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___f_3131_);
lean_ctor_set(v___x_3121_, 0, v___x_3139_);
v___x_3141_ = v___x_3121_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v___f_3131_);
v___x_3141_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; lean_object* v___x_909__overap_3146_; lean_object* v___x_3147_; 
v___x_3142_ = l_StateRefT_x27_instMonad___redArg(v___x_3141_);
v___x_3143_ = l_Lean_instInhabitedExpr;
v___x_3144_ = l_instInhabitedOfMonad___redArg(v___x_3142_, v___x_3143_);
v___f_3145_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3145_, 0, v___x_3144_);
v___x_909__overap_3146_ = lean_panic_fn_borrowed(v___f_3145_, v_msg_3085_);
lean_dec_ref(v___f_3145_);
lean_inc(v___y_3091_);
lean_inc_ref(v___y_3090_);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3088_);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
v___x_3147_ = lean_apply_7(v___x_909__overap_3146_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, lean_box(0));
return v___x_3147_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3169_, lean_object* v_vals_3170_, lean_object* v_i_3171_, lean_object* v_k_3172_){
_start:
{
lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3173_ = lean_array_get_size(v_keys_3169_);
v___x_3174_ = lean_nat_dec_lt(v_i_3171_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_dec_ref(v_k_3172_);
lean_dec(v_i_3171_);
v___x_3175_ = lean_box(0);
return v___x_3175_;
}
else
{
lean_object* v_k_x27_3176_; uint8_t v___x_3177_; 
v_k_x27_3176_ = lean_array_fget_borrowed(v_keys_3169_, v_i_3171_);
lean_inc(v_k_x27_3176_);
lean_inc_ref(v_k_3172_);
v___x_3177_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3172_, v_k_x27_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_unsigned_to_nat(1u);
v___x_3179_ = lean_nat_add(v_i_3171_, v___x_3178_);
lean_dec(v_i_3171_);
v_i_3171_ = v___x_3179_;
goto _start;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref(v_k_3172_);
v___x_3181_ = lean_array_fget_borrowed(v_vals_3170_, v_i_3171_);
lean_dec(v_i_3171_);
lean_inc(v___x_3181_);
lean_inc(v_k_x27_3176_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_k_x27_3176_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3184_, lean_object* v_vals_3185_, lean_object* v_i_3186_, lean_object* v_k_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3184_, v_vals_3185_, v_i_3186_, v_k_3187_);
lean_dec_ref(v_vals_3185_);
lean_dec_ref(v_keys_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3189_, size_t v_x_3190_, lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 0)
{
lean_object* v_es_3192_; lean_object* v___x_3193_; size_t v___x_3194_; size_t v___x_3195_; lean_object* v_j_3196_; lean_object* v___x_3197_; 
v_es_3192_ = lean_ctor_get(v_x_3189_, 0);
lean_inc_ref(v_es_3192_);
lean_dec_ref_known(v_x_3189_, 1);
v___x_3193_ = lean_box(2);
v___x_3194_ = ((size_t)31ULL);
v___x_3195_ = lean_usize_land(v_x_3190_, v___x_3194_);
v_j_3196_ = lean_usize_to_nat(v___x_3195_);
v___x_3197_ = lean_array_get(v___x_3193_, v_es_3192_, v_j_3196_);
lean_dec(v_j_3196_);
lean_dec_ref(v_es_3192_);
switch(lean_obj_tag(v___x_3197_))
{
case 0:
{
lean_object* v_key_3198_; lean_object* v_val_3199_; uint8_t v___x_3200_; 
v_key_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_n(v_key_3198_, 2);
v_val_3199_ = lean_ctor_get(v___x_3197_, 1);
lean_inc(v_val_3199_);
lean_dec_ref_known(v___x_3197_, 2);
v___x_3200_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3191_, v_key_3198_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_dec(v_val_3199_);
lean_dec(v_key_3198_);
v___x_3201_ = lean_box(0);
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_key_3198_);
lean_ctor_set(v___x_3202_, 1, v_val_3199_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
case 1:
{
lean_object* v_node_3204_; size_t v___x_3205_; size_t v___x_3206_; 
v_node_3204_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_node_3204_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3205_ = ((size_t)5ULL);
v___x_3206_ = lean_usize_shift_right(v_x_3190_, v___x_3205_);
v_x_3189_ = v_node_3204_;
v_x_3190_ = v___x_3206_;
goto _start;
}
default: 
{
lean_object* v___x_3208_; 
lean_dec_ref(v_x_3191_);
v___x_3208_ = lean_box(0);
return v___x_3208_;
}
}
}
else
{
lean_object* v_ks_3209_; lean_object* v_vs_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_ks_3209_ = lean_ctor_get(v_x_3189_, 0);
lean_inc_ref(v_ks_3209_);
v_vs_3210_ = lean_ctor_get(v_x_3189_, 1);
lean_inc_ref(v_vs_3210_);
lean_dec_ref_known(v_x_3189_, 2);
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3209_, v_vs_3210_, v___x_3211_, v_x_3191_);
lean_dec_ref(v_vs_3210_);
lean_dec_ref(v_ks_3209_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
size_t v_x_1226__boxed_3216_; lean_object* v_res_3217_; 
v_x_1226__boxed_3216_ = lean_unbox_usize(v_x_3214_);
lean_dec(v_x_3214_);
v_res_3217_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3213_, v_x_1226__boxed_3216_, v_x_3215_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3218_, lean_object* v_x_3219_){
_start:
{
uint64_t v___x_3220_; size_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3219_);
v___x_3221_ = lean_uint64_to_usize(v___x_3220_);
lean_inc_ref(v_x_3218_);
v___x_3222_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3218_, v___x_3221_, v_x_3219_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3223_, v_x_3224_);
lean_dec_ref(v_x_3223_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3226_, lean_object* v_cache_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3230_; 
lean_inc_ref(v_e_3226_);
v___x_3230_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3229_, v_e_3226_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_cache_3227_);
lean_ctor_set(v___x_3231_, 1, v___y_3229_);
v___x_3232_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3226_, v___y_3228_, v___x_3231_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3242_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 1);
v_a_3234_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3236_ = v___x_3232_;
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3233_);
lean_inc(v_a_3234_);
lean_dec(v___x_3232_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v_set_3238_; lean_object* v___x_3240_; 
v_set_3238_ = lean_ctor_get(v_a_3233_, 1);
lean_inc_ref(v_set_3238_);
lean_dec(v_a_3233_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 1, v_set_3238_);
v___x_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3234_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_set_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3252_; 
v_a_3243_ = lean_ctor_get(v___x_3232_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3253_);
v___x_3245_ = v___x_3232_;
v_isShared_3246_ = v_isSharedCheck_3252_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3232_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3252_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_map_3247_; lean_object* v_set_3248_; lean_object* v___x_3250_; 
v_map_3247_ = lean_ctor_get(v_a_3243_, 0);
lean_inc_ref(v_map_3247_);
v_set_3248_ = lean_ctor_get(v_a_3243_, 1);
lean_inc_ref(v_set_3248_);
lean_dec(v_a_3243_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 1, v_set_3248_);
lean_ctor_set(v___x_3245_, 0, v_map_3247_);
v___x_3250_ = v___x_3245_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_map_3247_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_set_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_val_3254_; lean_object* v_fst_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_cache_3227_);
lean_dec_ref(v_e_3226_);
v_val_3254_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v___x_3230_, 1);
v_fst_3255_ = lean_ctor_get(v_val_3254_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_val_3254_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; 
v_unused_3263_ = lean_ctor_get(v_val_3254_, 1);
lean_dec(v_unused_3263_);
v___x_3257_ = v_val_3254_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_fst_3255_);
lean_dec(v_val_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 1, v___y_3229_);
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_fst_3255_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___y_3229_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3264_, lean_object* v_cache_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3264_, v_cache_3265_, v___y_3266_, v___y_3267_);
lean_dec_ref(v___y_3266_);
return v_res_3268_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3270_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_3271_ = lean_unsigned_to_nat(16u);
v___x_3272_ = lean_unsigned_to_nat(396u);
v___x_3273_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3274_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3275_ = l_mkPanicMessageWithDecl(v___x_3274_, v___x_3273_, v___x_3272_, v___x_3271_, v___x_3270_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3276_, lean_object* v_cache_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3285_; lean_object* v_env_3286_; lean_object* v___f_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3301_; 
v___x_3285_ = lean_st_ref_get(v_a_3283_);
v_env_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc_ref(v_env_3286_);
lean_dec(v___x_3285_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3287_, 0, v_e_3276_);
lean_closure_set(v___f_3287_, 1, v_cache_3277_);
v___x_3288_ = 0;
v___x_3289_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3289_, 0, v_env_3286_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*1, v___x_3288_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*1 + 1, v___x_3288_);
v___x_3290_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3287_, v___x_3289_, v_a_3279_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3301_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3301_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
if (lean_obj_tag(v_a_3291_) == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec_ref_known(v_a_3291_, 1);
lean_del_object(v___x_3293_);
v___x_3295_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3296_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3295_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
return v___x_3296_;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; 
v_a_3297_ = lean_ctor_get(v_a_3291_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v_a_3291_, 1);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v_a_3297_);
v___x_3299_ = v___x_3293_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3302_, lean_object* v_cache_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3302_, v_cache_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3313_, v_x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3316_, v_x_3317_, v_x_3318_);
lean_dec_ref(v_x_3317_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3320_, lean_object* v_x_3321_, size_t v_x_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v___x_3324_; 
lean_inc_ref(v_x_3321_);
v___x_3324_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3321_, v_x_3322_, v_x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
size_t v_x_1431__boxed_3329_; lean_object* v_res_3330_; 
v_x_1431__boxed_3329_ = lean_unbox_usize(v_x_3327_);
lean_dec(v_x_3327_);
v_res_3330_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3325_, v_x_3326_, v_x_1431__boxed_3329_, v_x_3328_);
lean_dec_ref(v_x_3326_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3331_, lean_object* v_keys_3332_, lean_object* v_vals_3333_, lean_object* v_heq_3334_, lean_object* v_i_3335_, lean_object* v_k_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3332_, v_vals_3333_, v_i_3335_, v_k_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3338_, lean_object* v_keys_3339_, lean_object* v_vals_3340_, lean_object* v_heq_3341_, lean_object* v_i_3342_, lean_object* v_k_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3338_, v_keys_3339_, v_vals_3340_, v_heq_3341_, v_i_3342_, v_k_3343_);
lean_dec_ref(v_vals_3340_);
lean_dec_ref(v_keys_3339_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_ref_3351_; lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3361_; 
v_ref_3351_ = lean_ctor_get(v___y_3348_, 5);
v___x_3352_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
lean_inc(v_ref_3351_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v_ref_3351_);
lean_ctor_set(v___x_3357_, 1, v_a_3353_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 1);
lean_ctor_set(v___x_3355_, 0, v___x_3357_);
v___x_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3371_ = l_Lean_stringToMessageData(v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3372_, lean_object* v_cache_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; uint8_t v___x_3391_; 
v___x_3391_ = l_Lean_Expr_hasLooseBVars(v_e_3372_);
if (v___x_3391_ == 0)
{
v___y_3382_ = v_a_3374_;
v___y_3383_ = v_a_3375_;
v___y_3384_ = v_a_3376_;
v___y_3385_ = v_a_3377_;
v___y_3386_ = v_a_3378_;
v___y_3387_ = v_a_3379_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_cache_3373_);
v___x_3392_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3393_ = l_Lean_indentExpr(v_e_3372_);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3394_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
v___jp_3381_:
{
lean_object* v___x_3388_; 
v___x_3388_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3372_, v___y_3382_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3389_, v_cache_3373_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
return v___x_3390_;
}
else
{
lean_dec_ref(v_cache_3373_);
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3404_, lean_object* v_cache_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3404_, v_cache_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3414_, lean_object* v_msg_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3415_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3424_, lean_object* v_msg_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3424_, v_msg_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3434_, lean_object* v___x_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3438_; 
lean_inc_ref(v_e_3434_);
v___x_3438_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3437_, v_e_3434_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3435_);
lean_ctor_set(v___x_3439_, 1, v___y_3437_);
v___x_3440_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3434_, v___y_3436_, v___x_3439_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3450_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 1);
v_a_3442_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3444_ = v___x_3440_;
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3441_);
lean_inc(v_a_3442_);
lean_dec(v___x_3440_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v_set_3446_; lean_object* v___x_3448_; 
v_set_3446_ = lean_ctor_get(v_a_3441_, 1);
lean_inc_ref(v_set_3446_);
lean_dec(v_a_3441_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 1, v_set_3446_);
v___x_3448_ = v___x_3444_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3442_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_set_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3460_; 
v_a_3451_ = lean_ctor_get(v___x_3440_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3440_, 0);
lean_dec(v_unused_3461_);
v___x_3453_ = v___x_3440_;
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3440_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v_map_3455_; lean_object* v_set_3456_; lean_object* v___x_3458_; 
v_map_3455_ = lean_ctor_get(v_a_3451_, 0);
lean_inc_ref(v_map_3455_);
v_set_3456_ = lean_ctor_get(v_a_3451_, 1);
lean_inc_ref(v_set_3456_);
lean_dec(v_a_3451_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v_set_3456_);
lean_ctor_set(v___x_3453_, 0, v_map_3455_);
v___x_3458_ = v___x_3453_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_map_3455_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_set_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_object* v_val_3462_; lean_object* v_fst_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v___x_3435_);
lean_dec_ref(v_e_3434_);
v_val_3462_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_val_3462_);
lean_dec_ref_known(v___x_3438_, 1);
v_fst_3463_ = lean_ctor_get(v_val_3462_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_val_3462_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v_val_3462_, 1);
lean_dec(v_unused_3471_);
v___x_3465_ = v_val_3462_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_fst_3463_);
lean_dec(v_val_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v___y_3437_);
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_fst_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___y_3437_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3472_, lean_object* v___x_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3472_, v___x_3473_, v___y_3474_, v___y_3475_);
lean_dec_ref(v___y_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___x_3485_; lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v___f_3488_; lean_object* v___x_3489_; lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3500_; 
v___x_3485_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3478_, v_a_3483_);
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3477_);
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3488_, 0, v_e_3477_);
lean_closure_set(v___f_3488_, 1, v___x_3487_);
v___x_3489_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3488_, v_a_3486_, v_a_3479_);
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3500_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3500_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
if (lean_obj_tag(v_a_3490_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; 
lean_del_object(v___x_3492_);
v_a_3494_ = lean_ctor_get(v_a_3490_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v_a_3490_, 1);
v___x_3495_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3477_, v_a_3494_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
return v___x_3495_;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; 
lean_dec_ref(v_e_3477_);
v_a_3496_ = lean_ctor_get(v_a_3490_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v_a_3490_, 1);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_a_3496_);
v___x_3498_ = v___x_3492_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Meta_Sym_shareCommon(v_e_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3510_, v___y_3511_, v___y_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3514_, v___y_3515_, v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___x_3526_; lean_object* v_a_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3540_; 
v___x_3526_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3519_, v_a_3524_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3526_);
lean_inc_ref(v_e_3518_);
v___f_3528_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3528_, 0, v_e_3518_);
v___x_3529_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3528_, v_a_3527_, v_a_3520_);
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
if (lean_obj_tag(v_a_3530_) == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec_ref_known(v_a_3530_, 1);
lean_del_object(v___x_3532_);
v___x_3534_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3535_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3518_, v___x_3534_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
return v___x_3535_;
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; 
lean_dec_ref(v_e_3518_);
v_a_3536_ = lean_ctor_get(v_a_3530_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v_a_3530_, 1);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v_a_3536_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_Meta_Sym_share(v_e_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3568_){
_start:
{
lean_object* v___x_3570_; uint8_t v_debug_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3570_ = lean_st_ref_get(v_a_3568_);
v_debug_3571_ = lean_ctor_get_uint8(v___x_3570_, sizeof(void*)*11);
lean_dec(v___x_3570_);
v___x_3572_ = lean_box(v_debug_3571_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3574_);
lean_dec(v_a_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v___x_3584_; uint8_t v_debug_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3584_ = lean_st_ref_get(v_a_3578_);
v_debug_3585_ = lean_ctor_get_uint8(v___x_3584_, sizeof(void*)*11);
lean_dec(v___x_3584_);
v___x_3586_ = lean_box(v_debug_3585_);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3596_){
_start:
{
lean_object* v_config_3598_; lean_object* v___x_3599_; 
v_config_3598_ = lean_ctor_get(v_a_3596_, 1);
lean_inc_ref(v_config_3598_);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v_config_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3600_);
lean_dec_ref(v_a_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3603_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Meta_Sym_getConfig(v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3619_, lean_object* v_msg_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_ref_3626_; lean_object* v___x_3627_; lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3672_; 
v_ref_3626_ = lean_ctor_get(v___y_3623_, 5);
v___x_3627_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3672_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3672_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v_traceState_3633_; lean_object* v_env_3634_; lean_object* v_nextMacroScope_3635_; lean_object* v_ngen_3636_; lean_object* v_auxDeclNGen_3637_; lean_object* v_cache_3638_; lean_object* v_messages_3639_; lean_object* v_infoState_3640_; lean_object* v_snapshotTasks_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3671_; 
v___x_3632_ = lean_st_ref_take(v___y_3624_);
v_traceState_3633_ = lean_ctor_get(v___x_3632_, 4);
v_env_3634_ = lean_ctor_get(v___x_3632_, 0);
v_nextMacroScope_3635_ = lean_ctor_get(v___x_3632_, 1);
v_ngen_3636_ = lean_ctor_get(v___x_3632_, 2);
v_auxDeclNGen_3637_ = lean_ctor_get(v___x_3632_, 3);
v_cache_3638_ = lean_ctor_get(v___x_3632_, 5);
v_messages_3639_ = lean_ctor_get(v___x_3632_, 6);
v_infoState_3640_ = lean_ctor_get(v___x_3632_, 7);
v_snapshotTasks_3641_ = lean_ctor_get(v___x_3632_, 8);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3643_ = v___x_3632_;
v_isShared_3644_ = v_isSharedCheck_3671_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_snapshotTasks_3641_);
lean_inc(v_infoState_3640_);
lean_inc(v_messages_3639_);
lean_inc(v_cache_3638_);
lean_inc(v_traceState_3633_);
lean_inc(v_auxDeclNGen_3637_);
lean_inc(v_ngen_3636_);
lean_inc(v_nextMacroScope_3635_);
lean_inc(v_env_3634_);
lean_dec(v___x_3632_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3671_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
uint64_t v_tid_3645_; lean_object* v_traces_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3670_; 
v_tid_3645_ = lean_ctor_get_uint64(v_traceState_3633_, sizeof(void*)*1);
v_traces_3646_ = lean_ctor_get(v_traceState_3633_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_traceState_3633_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3648_ = v_traceState_3633_;
v_isShared_3649_ = v_isSharedCheck_3670_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_traces_3646_);
lean_dec(v_traceState_3633_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3670_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; double v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3650_ = lean_box(0);
v___x_3651_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3652_ = 0;
v___x_3653_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3654_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3654_, 0, v_cls_3619_);
lean_ctor_set(v___x_3654_, 1, v___x_3650_);
lean_ctor_set(v___x_3654_, 2, v___x_3653_);
lean_ctor_set_float(v___x_3654_, sizeof(void*)*3, v___x_3651_);
lean_ctor_set_float(v___x_3654_, sizeof(void*)*3 + 8, v___x_3651_);
lean_ctor_set_uint8(v___x_3654_, sizeof(void*)*3 + 16, v___x_3652_);
v___x_3655_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3656_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v_a_3628_);
lean_ctor_set(v___x_3656_, 2, v___x_3655_);
lean_inc(v_ref_3626_);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v_ref_3626_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_PersistentArray_push___redArg(v_traces_3646_, v___x_3657_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3658_);
v___x_3660_ = v___x_3648_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3658_);
lean_ctor_set_uint64(v_reuseFailAlloc_3669_, sizeof(void*)*1, v_tid_3645_);
v___x_3660_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3662_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 4, v___x_3660_);
v___x_3662_ = v___x_3643_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_env_3634_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_nextMacroScope_3635_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_ngen_3636_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_auxDeclNGen_3637_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3668_, 5, v_cache_3638_);
lean_ctor_set(v_reuseFailAlloc_3668_, 6, v_messages_3639_);
lean_ctor_set(v_reuseFailAlloc_3668_, 7, v_infoState_3640_);
lean_ctor_set(v_reuseFailAlloc_3668_, 8, v_snapshotTasks_3641_);
v___x_3662_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3663_ = lean_st_ref_set(v___y_3624_, v___x_3662_);
v___x_3664_ = lean_box(0);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3664_);
v___x_3666_ = v___x_3630_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3673_, lean_object* v_msg_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3673_, v_msg_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
return v_res_3680_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3684_; uint8_t v___x_3685_; double v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3684_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3685_ = 1;
v___x_3686_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3687_ = lean_box(0);
v___x_3688_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3689_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
lean_ctor_set(v___x_3689_, 1, v___x_3687_);
lean_ctor_set(v___x_3689_, 2, v___x_3684_);
lean_ctor_set_float(v___x_3689_, sizeof(void*)*3, v___x_3686_);
lean_ctor_set_float(v___x_3689_, sizeof(void*)*3 + 8, v___x_3686_);
lean_ctor_set_uint8(v___x_3689_, sizeof(void*)*3 + 16, v___x_3685_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v___x_3701_; lean_object* v_a_3702_; lean_object* v___x_3703_; lean_object* v_share_3704_; lean_object* v_maxFVar_3705_; lean_object* v_proofInstInfo_3706_; lean_object* v_inferType_3707_; lean_object* v_getLevel_3708_; lean_object* v_congrInfo_3709_; lean_object* v_defEqI_3710_; lean_object* v_extensions_3711_; lean_object* v_issues_3712_; lean_object* v_canon_3713_; lean_object* v_instanceOverrides_3714_; uint8_t v_debug_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3734_; 
v___x_3701_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3690_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref(v___x_3701_);
v___x_3703_ = lean_st_ref_take(v_a_3692_);
v_share_3704_ = lean_ctor_get(v___x_3703_, 0);
v_maxFVar_3705_ = lean_ctor_get(v___x_3703_, 1);
v_proofInstInfo_3706_ = lean_ctor_get(v___x_3703_, 2);
v_inferType_3707_ = lean_ctor_get(v___x_3703_, 3);
v_getLevel_3708_ = lean_ctor_get(v___x_3703_, 4);
v_congrInfo_3709_ = lean_ctor_get(v___x_3703_, 5);
v_defEqI_3710_ = lean_ctor_get(v___x_3703_, 6);
v_extensions_3711_ = lean_ctor_get(v___x_3703_, 7);
v_issues_3712_ = lean_ctor_get(v___x_3703_, 8);
v_canon_3713_ = lean_ctor_get(v___x_3703_, 9);
v_instanceOverrides_3714_ = lean_ctor_get(v___x_3703_, 10);
v_debug_3715_ = lean_ctor_get_uint8(v___x_3703_, sizeof(void*)*11);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3717_ = v___x_3703_;
v_isShared_3718_ = v_isSharedCheck_3734_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_instanceOverrides_3714_);
lean_inc(v_canon_3713_);
lean_inc(v_issues_3712_);
lean_inc(v_extensions_3711_);
lean_inc(v_defEqI_3710_);
lean_inc(v_congrInfo_3709_);
lean_inc(v_getLevel_3708_);
lean_inc(v_inferType_3707_);
lean_inc(v_proofInstInfo_3706_);
lean_inc(v_maxFVar_3705_);
lean_inc(v_share_3704_);
lean_dec(v___x_3703_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3734_;
goto v_resetjp_3716_;
}
v___jp_3698_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3719_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3720_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3702_);
v___x_3721_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v_a_3702_);
lean_ctor_set(v___x_3721_, 2, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v_issues_3712_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 8, v___x_3722_);
v___x_3724_ = v___x_3717_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_share_3704_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_maxFVar_3705_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_proofInstInfo_3706_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_inferType_3707_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_getLevel_3708_);
lean_ctor_set(v_reuseFailAlloc_3733_, 5, v_congrInfo_3709_);
lean_ctor_set(v_reuseFailAlloc_3733_, 6, v_defEqI_3710_);
lean_ctor_set(v_reuseFailAlloc_3733_, 7, v_extensions_3711_);
lean_ctor_set(v_reuseFailAlloc_3733_, 8, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3733_, 9, v_canon_3713_);
lean_ctor_set(v_reuseFailAlloc_3733_, 10, v_instanceOverrides_3714_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*11, v_debug_3715_);
v___x_3724_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v_options_3726_; uint8_t v_hasTrace_3727_; 
v___x_3725_ = lean_st_ref_set(v_a_3692_, v___x_3724_);
v_options_3726_ = lean_ctor_get(v_a_3695_, 2);
v_hasTrace_3727_ = lean_ctor_get_uint8(v_options_3726_, sizeof(void*)*1);
if (v_hasTrace_3727_ == 0)
{
lean_dec(v_a_3702_);
goto v___jp_3698_;
}
else
{
lean_object* v_inheritedTraceOptions_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v_inheritedTraceOptions_3728_ = lean_ctor_get(v_a_3695_, 13);
v___x_3729_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3730_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3728_, v_options_3726_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_dec(v_a_3702_);
goto v___jp_3698_;
}
else
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3729_, v_a_3702_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
return v___x_3732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Meta_Sym_reportIssue(v_msg_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3744_, lean_object* v_msg_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3744_, v_msg_3745_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3754_, lean_object* v_msg_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3754_, v_msg_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v___x_3772_; lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3783_; 
v___x_3772_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3765_);
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3783_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3783_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
uint8_t v_verbose_3777_; 
v_verbose_3777_ = lean_ctor_get_uint8(v_a_3773_, 0);
lean_dec(v_a_3773_);
if (v_verbose_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_dec_ref(v_msg_3764_);
v___x_3778_ = lean_box(0);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 0, v___x_3778_);
v___x_3780_ = v___x_3775_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
else
{
lean_object* v___x_3782_; 
lean_del_object(v___x_3775_);
v___x_3782_ = l_Lean_Meta_Sym_reportIssue(v_msg_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
return v___x_3782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
return v_res_3792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3809_ = l_String_toRawSubstring_x27(v___x_3808_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3848_ = l_String_toRawSubstring_x27(v___x_3847_);
return v___x_3848_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3861_ = l_String_toRawSubstring_x27(v___x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_msg_3888_; lean_object* v_quotContext_3889_; lean_object* v_currMacroScope_3890_; lean_object* v_ref_3891_; lean_object* v___y_3892_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
lean_inc(v_s_3884_);
v___x_3907_ = l_Lean_Syntax_getKind(v_s_3884_);
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3909_ = lean_name_eq(v___x_3907_, v___x_3908_);
lean_dec(v___x_3907_);
if (v___x_3909_ == 0)
{
lean_object* v_quotContext_3910_; lean_object* v_currMacroScope_3911_; lean_object* v_ref_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_quotContext_3910_ = lean_ctor_get(v_a_3885_, 1);
v_currMacroScope_3911_ = lean_ctor_get(v_a_3885_, 2);
v_ref_3912_ = lean_ctor_get(v_a_3885_, 5);
v___x_3913_ = l_Lean_SourceInfo_fromRef(v_ref_3912_, v___x_3909_);
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3915_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3913_, 8);
v___x_3917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3913_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3919_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3920_ = lean_box(0);
lean_inc_n(v_currMacroScope_3911_, 3);
lean_inc_n(v_quotContext_3910_, 3);
v___x_3921_ = l_Lean_addMacroScope(v_quotContext_3910_, v___x_3920_, v_currMacroScope_3911_);
v___x_3922_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3913_);
lean_ctor_set(v___x_3923_, 1, v___x_3919_);
lean_ctor_set(v___x_3923_, 2, v___x_3921_);
lean_ctor_set(v___x_3923_, 3, v___x_3922_);
v___x_3924_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3918_, v___x_3923_);
v___x_3925_ = l_Lean_Syntax_node2(v___x_3913_, v___x_3915_, v___x_3917_, v___x_3924_);
v___x_3926_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_3927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3913_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3929_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_3930_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_3931_ = l_Lean_addMacroScope(v_quotContext_3910_, v___x_3930_, v_currMacroScope_3911_);
v___x_3932_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_3933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3913_);
lean_ctor_set(v___x_3933_, 1, v___x_3929_);
lean_ctor_set(v___x_3933_, 2, v___x_3931_);
lean_ctor_set(v___x_3933_, 3, v___x_3932_);
v___x_3934_ = l_Lean_Syntax_node1(v___x_3913_, v___x_3928_, v___x_3933_);
v___x_3935_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_3936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3913_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l_Lean_Syntax_node5(v___x_3913_, v___x_3914_, v___x_3925_, v_s_3884_, v___x_3927_, v___x_3934_, v___x_3936_);
v_msg_3888_ = v___x_3937_;
v_quotContext_3889_ = v_quotContext_3910_;
v_currMacroScope_3890_ = v_currMacroScope_3911_;
v_ref_3891_ = v_ref_3912_;
v___y_3892_ = v_a_3886_;
goto v___jp_3887_;
}
else
{
lean_object* v_quotContext_3938_; lean_object* v_currMacroScope_3939_; lean_object* v_ref_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_quotContext_3938_ = lean_ctor_get(v_a_3885_, 1);
v_currMacroScope_3939_ = lean_ctor_get(v_a_3885_, 2);
v_ref_3940_ = lean_ctor_get(v_a_3885_, 5);
v___x_3941_ = 0;
v___x_3942_ = l_Lean_SourceInfo_fromRef(v_ref_3940_, v___x_3941_);
v___x_3943_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_3944_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_3942_);
v___x_3945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3942_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_node2(v___x_3942_, v___x_3943_, v___x_3945_, v_s_3884_);
lean_inc(v_currMacroScope_3939_);
lean_inc(v_quotContext_3938_);
v_msg_3888_ = v___x_3946_;
v_quotContext_3889_ = v_quotContext_3938_;
v_currMacroScope_3890_ = v_currMacroScope_3939_;
v_ref_3891_ = v_ref_3940_;
v___y_3892_ = v_a_3886_;
goto v___jp_3887_;
}
v___jp_3887_:
{
uint8_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3893_ = 0;
v___x_3894_ = l_Lean_SourceInfo_fromRef(v_ref_3891_, v___x_3893_);
v___x_3895_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3896_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3897_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3899_ = l_Lean_addMacroScope(v_quotContext_3889_, v___x_3898_, v_currMacroScope_3890_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3894_, 3);
v___x_3901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3894_);
lean_ctor_set(v___x_3901_, 1, v___x_3897_);
lean_ctor_set(v___x_3901_, 2, v___x_3899_);
lean_ctor_set(v___x_3901_, 3, v___x_3900_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3903_ = l_Lean_Syntax_node1(v___x_3894_, v___x_3902_, v_msg_3888_);
v___x_3904_ = l_Lean_Syntax_node2(v___x_3894_, v___x_3896_, v___x_3901_, v___x_3903_);
v___x_3905_ = l_Lean_Syntax_node1(v___x_3894_, v___x_3895_, v___x_3904_);
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v___y_3892_);
return v___x_3906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_3947_, v_a_3948_, v_a_3949_);
lean_dec_ref(v_a_3948_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v___x_3994_; uint8_t v___x_3995_; 
v___x_3994_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_3991_);
v___x_3995_ = l_Lean_Syntax_isOfKind(v_x_3991_, v___x_3994_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_dec(v_x_3991_);
v___x_3996_ = lean_box(1);
v___x_3997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set(v___x_3997_, 1, v_a_3993_);
return v___x_3997_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v_a_4001_; lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = l_Lean_Syntax_getArg(v_x_3991_, v___x_3998_);
lean_dec(v_x_3991_);
v___x_4000_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_3999_, v_a_3992_, v_a_3993_);
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
v_a_4002_ = lean_ctor_get(v___x_4000_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_4000_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_inc(v_a_4001_);
lean_dec(v___x_4000_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4001_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4010_, v_a_4011_, v_a_4012_);
lean_dec_ref(v_a_4011_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v___x_4022_; lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4042_; 
v___x_4022_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4015_);
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4042_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4042_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
uint8_t v_verbose_4027_; 
v_verbose_4027_ = lean_ctor_get_uint8(v_a_4023_, 0);
lean_dec(v_a_4023_);
if (v_verbose_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
lean_dec_ref(v_msg_4014_);
v___x_4028_ = lean_box(0);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4028_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
else
{
lean_object* v_options_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_options_4032_ = lean_ctor_get(v_a_4019_, 2);
v___x_4033_ = l_Lean_KVMap_instValueBool;
v___x_4034_ = l_Lean_Meta_Sym_sym_debug;
v___x_4035_ = l_Lean_Option_get___redArg(v___x_4033_, v_options_4032_, v___x_4034_);
v___x_4036_ = lean_unbox(v___x_4035_);
lean_dec(v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
lean_dec_ref(v_msg_4014_);
v___x_4037_ = lean_box(0);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4037_);
v___x_4039_ = v___x_4025_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
else
{
lean_object* v___x_4041_; 
lean_del_object(v___x_4025_);
v___x_4041_ = l_Lean_Meta_Sym_reportIssue(v_msg_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v___x_4041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
return v_res_4051_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4054_ = l_String_toRawSubstring_x27(v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_msg_4074_; lean_object* v_quotContext_4075_; lean_object* v_currMacroScope_4076_; lean_object* v_ref_4077_; lean_object* v___y_4078_; lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
lean_inc(v_s_4070_);
v___x_4093_ = l_Lean_Syntax_getKind(v_s_4070_);
v___x_4094_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4095_ = lean_name_eq(v___x_4093_, v___x_4094_);
lean_dec(v___x_4093_);
if (v___x_4095_ == 0)
{
lean_object* v_quotContext_4096_; lean_object* v_currMacroScope_4097_; lean_object* v_ref_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_quotContext_4096_ = lean_ctor_get(v_a_4071_, 1);
v_currMacroScope_4097_ = lean_ctor_get(v_a_4071_, 2);
v_ref_4098_ = lean_ctor_get(v_a_4071_, 5);
v___x_4099_ = l_Lean_SourceInfo_fromRef(v_ref_4098_, v___x_4095_);
v___x_4100_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4101_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4099_, 8);
v___x_4103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4099_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4105_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4106_ = lean_box(0);
lean_inc_n(v_currMacroScope_4097_, 3);
lean_inc_n(v_quotContext_4096_, 3);
v___x_4107_ = l_Lean_addMacroScope(v_quotContext_4096_, v___x_4106_, v_currMacroScope_4097_);
v___x_4108_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4109_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4099_);
lean_ctor_set(v___x_4109_, 1, v___x_4105_);
lean_ctor_set(v___x_4109_, 2, v___x_4107_);
lean_ctor_set(v___x_4109_, 3, v___x_4108_);
v___x_4110_ = l_Lean_Syntax_node1(v___x_4099_, v___x_4104_, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node2(v___x_4099_, v___x_4101_, v___x_4103_, v___x_4110_);
v___x_4112_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4099_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4115_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4116_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4117_ = l_Lean_addMacroScope(v_quotContext_4096_, v___x_4116_, v_currMacroScope_4097_);
v___x_4118_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4119_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4099_);
lean_ctor_set(v___x_4119_, 1, v___x_4115_);
lean_ctor_set(v___x_4119_, 2, v___x_4117_);
lean_ctor_set(v___x_4119_, 3, v___x_4118_);
v___x_4120_ = l_Lean_Syntax_node1(v___x_4099_, v___x_4114_, v___x_4119_);
v___x_4121_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4099_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_Syntax_node5(v___x_4099_, v___x_4100_, v___x_4111_, v_s_4070_, v___x_4113_, v___x_4120_, v___x_4122_);
v_msg_4074_ = v___x_4123_;
v_quotContext_4075_ = v_quotContext_4096_;
v_currMacroScope_4076_ = v_currMacroScope_4097_;
v_ref_4077_ = v_ref_4098_;
v___y_4078_ = v_a_4072_;
goto v___jp_4073_;
}
else
{
lean_object* v_quotContext_4124_; lean_object* v_currMacroScope_4125_; lean_object* v_ref_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_quotContext_4124_ = lean_ctor_get(v_a_4071_, 1);
v_currMacroScope_4125_ = lean_ctor_get(v_a_4071_, 2);
v_ref_4126_ = lean_ctor_get(v_a_4071_, 5);
v___x_4127_ = 0;
v___x_4128_ = l_Lean_SourceInfo_fromRef(v_ref_4126_, v___x_4127_);
v___x_4129_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4130_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4128_);
v___x_4131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4128_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_Syntax_node2(v___x_4128_, v___x_4129_, v___x_4131_, v_s_4070_);
lean_inc(v_currMacroScope_4125_);
lean_inc(v_quotContext_4124_);
v_msg_4074_ = v___x_4132_;
v_quotContext_4075_ = v_quotContext_4124_;
v_currMacroScope_4076_ = v_currMacroScope_4125_;
v_ref_4077_ = v_ref_4126_;
v___y_4078_ = v_a_4072_;
goto v___jp_4073_;
}
v___jp_4073_:
{
uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4079_ = 0;
v___x_4080_ = l_Lean_SourceInfo_fromRef(v_ref_4077_, v___x_4079_);
v___x_4081_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4083_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4084_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4085_ = l_Lean_addMacroScope(v_quotContext_4075_, v___x_4084_, v_currMacroScope_4076_);
v___x_4086_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4080_, 3);
v___x_4087_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4080_);
lean_ctor_set(v___x_4087_, 1, v___x_4083_);
lean_ctor_set(v___x_4087_, 2, v___x_4085_);
lean_ctor_set(v___x_4087_, 3, v___x_4086_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4089_ = l_Lean_Syntax_node1(v___x_4080_, v___x_4088_, v_msg_4074_);
v___x_4090_ = l_Lean_Syntax_node2(v___x_4080_, v___x_4082_, v___x_4087_, v___x_4089_);
v___x_4091_ = l_Lean_Syntax_node1(v___x_4080_, v___x_4081_, v___x_4090_);
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
lean_ctor_set(v___x_4092_, 1, v___y_4078_);
return v___x_4092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4133_, v_a_4134_, v_a_4135_);
lean_dec_ref(v_a_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___x_4158_; uint8_t v___x_4159_; 
v___x_4158_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4155_);
v___x_4159_ = l_Lean_Syntax_isOfKind(v_x_4155_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec(v_x_4155_);
v___x_4160_ = lean_box(1);
v___x_4161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
lean_ctor_set(v___x_4161_, 1, v_a_4157_);
return v___x_4161_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v_a_4165_; lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4163_ = l_Lean_Syntax_getArg(v_x_4155_, v___x_4162_);
lean_dec(v_x_4155_);
v___x_4164_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4163_, v_a_4156_, v_a_4157_);
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_a_4166_ = lean_ctor_get(v___x_4164_, 1);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4164_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4165_);
lean_ctor_set(v_reuseFailAlloc_4172_, 1, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4174_, v_a_4175_, v_a_4176_);
lean_dec_ref(v_a_4175_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v_issues_4181_; lean_object* v___x_4182_; 
v___x_4180_ = lean_st_ref_get(v_a_4178_);
v_issues_4181_ = lean_ctor_get(v___x_4180_, 8);
lean_inc(v_issues_4181_);
lean_dec(v___x_4180_);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v_issues_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4183_);
lean_dec(v_a_4183_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4187_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Meta_Sym_getIssues(v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4202_, lean_object* v_issues_4203_, lean_object* v_a_x3f_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v_share_4207_; lean_object* v_maxFVar_4208_; lean_object* v_proofInstInfo_4209_; lean_object* v_inferType_4210_; lean_object* v_getLevel_4211_; lean_object* v_congrInfo_4212_; lean_object* v_defEqI_4213_; lean_object* v_extensions_4214_; lean_object* v_issues_4215_; lean_object* v_canon_4216_; lean_object* v_instanceOverrides_4217_; uint8_t v_debug_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4229_; 
v___x_4206_ = lean_st_ref_take(v_a_4202_);
v_share_4207_ = lean_ctor_get(v___x_4206_, 0);
v_maxFVar_4208_ = lean_ctor_get(v___x_4206_, 1);
v_proofInstInfo_4209_ = lean_ctor_get(v___x_4206_, 2);
v_inferType_4210_ = lean_ctor_get(v___x_4206_, 3);
v_getLevel_4211_ = lean_ctor_get(v___x_4206_, 4);
v_congrInfo_4212_ = lean_ctor_get(v___x_4206_, 5);
v_defEqI_4213_ = lean_ctor_get(v___x_4206_, 6);
v_extensions_4214_ = lean_ctor_get(v___x_4206_, 7);
v_issues_4215_ = lean_ctor_get(v___x_4206_, 8);
v_canon_4216_ = lean_ctor_get(v___x_4206_, 9);
v_instanceOverrides_4217_ = lean_ctor_get(v___x_4206_, 10);
v_debug_4218_ = lean_ctor_get_uint8(v___x_4206_, sizeof(void*)*11);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4220_ = v___x_4206_;
v_isShared_4221_ = v_isSharedCheck_4229_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_instanceOverrides_4217_);
lean_inc(v_canon_4216_);
lean_inc(v_issues_4215_);
lean_inc(v_extensions_4214_);
lean_inc(v_defEqI_4213_);
lean_inc(v_congrInfo_4212_);
lean_inc(v_getLevel_4211_);
lean_inc(v_inferType_4210_);
lean_inc(v_proofInstInfo_4209_);
lean_inc(v_maxFVar_4208_);
lean_inc(v_share_4207_);
lean_dec(v___x_4206_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4229_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4222_ = l_List_appendTR___redArg(v_issues_4215_, v_issues_4203_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 8, v___x_4222_);
v___x_4224_ = v___x_4220_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_share_4207_);
lean_ctor_set(v_reuseFailAlloc_4228_, 1, v_maxFVar_4208_);
lean_ctor_set(v_reuseFailAlloc_4228_, 2, v_proofInstInfo_4209_);
lean_ctor_set(v_reuseFailAlloc_4228_, 3, v_inferType_4210_);
lean_ctor_set(v_reuseFailAlloc_4228_, 4, v_getLevel_4211_);
lean_ctor_set(v_reuseFailAlloc_4228_, 5, v_congrInfo_4212_);
lean_ctor_set(v_reuseFailAlloc_4228_, 6, v_defEqI_4213_);
lean_ctor_set(v_reuseFailAlloc_4228_, 7, v_extensions_4214_);
lean_ctor_set(v_reuseFailAlloc_4228_, 8, v___x_4222_);
lean_ctor_set(v_reuseFailAlloc_4228_, 9, v_canon_4216_);
lean_ctor_set(v_reuseFailAlloc_4228_, 10, v_instanceOverrides_4217_);
lean_ctor_set_uint8(v_reuseFailAlloc_4228_, sizeof(void*)*11, v_debug_4218_);
v___x_4224_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = lean_st_ref_set(v_a_4202_, v___x_4224_);
v___x_4226_ = lean_box(0);
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
return v___x_4227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4230_, lean_object* v_issues_4231_, lean_object* v_a_x3f_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4230_, v_issues_4231_, v_a_x3f_4232_);
lean_dec(v_a_x3f_4232_);
lean_dec(v_a_4230_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_share_4245_; lean_object* v_maxFVar_4246_; lean_object* v_proofInstInfo_4247_; lean_object* v_inferType_4248_; lean_object* v_getLevel_4249_; lean_object* v_congrInfo_4250_; lean_object* v_defEqI_4251_; lean_object* v_extensions_4252_; lean_object* v_canon_4253_; lean_object* v_instanceOverrides_4254_; uint8_t v_debug_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4294_; 
v___x_4243_ = lean_st_ref_get(v_a_4237_);
v___x_4244_ = lean_st_ref_take(v_a_4237_);
v_share_4245_ = lean_ctor_get(v___x_4244_, 0);
v_maxFVar_4246_ = lean_ctor_get(v___x_4244_, 1);
v_proofInstInfo_4247_ = lean_ctor_get(v___x_4244_, 2);
v_inferType_4248_ = lean_ctor_get(v___x_4244_, 3);
v_getLevel_4249_ = lean_ctor_get(v___x_4244_, 4);
v_congrInfo_4250_ = lean_ctor_get(v___x_4244_, 5);
v_defEqI_4251_ = lean_ctor_get(v___x_4244_, 6);
v_extensions_4252_ = lean_ctor_get(v___x_4244_, 7);
v_canon_4253_ = lean_ctor_get(v___x_4244_, 9);
v_instanceOverrides_4254_ = lean_ctor_get(v___x_4244_, 10);
v_debug_4255_ = lean_ctor_get_uint8(v___x_4244_, sizeof(void*)*11);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4294_ == 0)
{
lean_object* v_unused_4295_; 
v_unused_4295_ = lean_ctor_get(v___x_4244_, 8);
lean_dec(v_unused_4295_);
v___x_4257_ = v___x_4244_;
v_isShared_4258_ = v_isSharedCheck_4294_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_instanceOverrides_4254_);
lean_inc(v_canon_4253_);
lean_inc(v_extensions_4252_);
lean_inc(v_defEqI_4251_);
lean_inc(v_congrInfo_4250_);
lean_inc(v_getLevel_4249_);
lean_inc(v_inferType_4248_);
lean_inc(v_proofInstInfo_4247_);
lean_inc(v_maxFVar_4246_);
lean_inc(v_share_4245_);
lean_dec(v___x_4244_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4294_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4259_ = lean_box(0);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 8, v___x_4259_);
v___x_4261_ = v___x_4257_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_share_4245_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_maxFVar_4246_);
lean_ctor_set(v_reuseFailAlloc_4293_, 2, v_proofInstInfo_4247_);
lean_ctor_set(v_reuseFailAlloc_4293_, 3, v_inferType_4248_);
lean_ctor_set(v_reuseFailAlloc_4293_, 4, v_getLevel_4249_);
lean_ctor_set(v_reuseFailAlloc_4293_, 5, v_congrInfo_4250_);
lean_ctor_set(v_reuseFailAlloc_4293_, 6, v_defEqI_4251_);
lean_ctor_set(v_reuseFailAlloc_4293_, 7, v_extensions_4252_);
lean_ctor_set(v_reuseFailAlloc_4293_, 8, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4293_, 9, v_canon_4253_);
lean_ctor_set(v_reuseFailAlloc_4293_, 10, v_instanceOverrides_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4293_, sizeof(void*)*11, v_debug_4255_);
v___x_4261_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4262_; lean_object* v_issues_4263_; lean_object* v_r_4264_; 
v___x_4262_ = lean_st_ref_set(v_a_4237_, v___x_4261_);
v_issues_4263_ = lean_ctor_get(v___x_4243_, 8);
lean_inc(v_issues_4263_);
lean_dec(v___x_4243_);
lean_inc(v_a_4241_);
lean_inc_ref(v_a_4240_);
lean_inc(v_a_4239_);
lean_inc_ref(v_a_4238_);
lean_inc(v_a_4237_);
lean_inc_ref(v_a_4236_);
v_r_4264_ = lean_apply_7(v_x_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, lean_box(0));
if (lean_obj_tag(v_r_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4281_; 
v_a_4265_ = lean_ctor_get(v_r_4264_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v_r_4264_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4267_ = v_r_4264_;
v_isShared_4268_ = v_isSharedCheck_4281_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v_r_4264_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4281_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
lean_inc(v_a_4265_);
if (v_isShared_4268_ == 0)
{
lean_ctor_set_tag(v___x_4267_, 1);
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
v___x_4271_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4237_, v_issues_4263_, v___x_4270_);
lean_dec_ref(v___x_4270_);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4278_ == 0)
{
lean_object* v_unused_4279_; 
v_unused_4279_ = lean_ctor_get(v___x_4271_, 0);
lean_dec(v_unused_4279_);
v___x_4273_ = v___x_4271_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_dec(v___x_4271_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v_a_4265_);
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4265_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
v_a_4282_ = lean_ctor_get(v_r_4264_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v_r_4264_, 1);
v___x_4283_ = lean_box(0);
v___x_4284_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4237_, v_issues_4263_, v___x_4283_);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4291_ == 0)
{
lean_object* v_unused_4292_; 
v_unused_4292_ = lean_ctor_get(v___x_4284_, 0);
lean_dec(v_unused_4292_);
v___x_4286_ = v___x_4284_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_dec(v___x_4284_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
lean_ctor_set_tag(v___x_4286_, 1);
lean_ctor_set(v___x_4286_, 0, v_a_4282_);
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4282_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4305_, lean_object* v_x_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4315_, lean_object* v_x_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4315_, v_x_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4325_, lean_object* v_vals_4326_, lean_object* v_i_4327_, lean_object* v_k_4328_){
_start:
{
uint8_t v___y_4330_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = lean_array_get_size(v_keys_4325_);
v___x_4337_ = lean_nat_dec_lt(v_i_4327_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_dec(v_i_4327_);
v___x_4338_ = lean_box(0);
return v___x_4338_;
}
else
{
lean_object* v_fst_4339_; lean_object* v_snd_4340_; lean_object* v_k_x27_4341_; lean_object* v_fst_4342_; lean_object* v_snd_4343_; uint8_t v___x_4344_; 
v_fst_4339_ = lean_ctor_get(v_k_4328_, 0);
v_snd_4340_ = lean_ctor_get(v_k_4328_, 1);
v_k_x27_4341_ = lean_array_fget_borrowed(v_keys_4325_, v_i_4327_);
v_fst_4342_ = lean_ctor_get(v_k_x27_4341_, 0);
v_snd_4343_ = lean_ctor_get(v_k_x27_4341_, 1);
v___x_4344_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4339_, v_fst_4342_);
if (v___x_4344_ == 0)
{
v___y_4330_ = v___x_4344_;
goto v___jp_4329_;
}
else
{
uint8_t v___x_4345_; 
v___x_4345_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4340_, v_snd_4343_);
v___y_4330_ = v___x_4345_;
goto v___jp_4329_;
}
}
v___jp_4329_:
{
if (v___y_4330_ == 0)
{
lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4331_ = lean_unsigned_to_nat(1u);
v___x_4332_ = lean_nat_add(v_i_4327_, v___x_4331_);
lean_dec(v_i_4327_);
v_i_4327_ = v___x_4332_;
goto _start;
}
else
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_array_fget_borrowed(v_vals_4326_, v_i_4327_);
lean_dec(v_i_4327_);
lean_inc(v___x_4334_);
v___x_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
return v___x_4335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4346_, lean_object* v_vals_4347_, lean_object* v_i_4348_, lean_object* v_k_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4346_, v_vals_4347_, v_i_4348_, v_k_4349_);
lean_dec_ref(v_k_4349_);
lean_dec_ref(v_vals_4347_);
lean_dec_ref(v_keys_4346_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4351_, size_t v_x_4352_, lean_object* v_x_4353_){
_start:
{
if (lean_obj_tag(v_x_4351_) == 0)
{
lean_object* v_es_4354_; lean_object* v___x_4355_; size_t v___x_4356_; size_t v___x_4357_; lean_object* v_j_4358_; lean_object* v___x_4359_; 
v_es_4354_ = lean_ctor_get(v_x_4351_, 0);
v___x_4355_ = lean_box(2);
v___x_4356_ = ((size_t)31ULL);
v___x_4357_ = lean_usize_land(v_x_4352_, v___x_4356_);
v_j_4358_ = lean_usize_to_nat(v___x_4357_);
v___x_4359_ = lean_array_get_borrowed(v___x_4355_, v_es_4354_, v_j_4358_);
lean_dec(v_j_4358_);
switch(lean_obj_tag(v___x_4359_))
{
case 0:
{
lean_object* v_key_4360_; lean_object* v_val_4361_; uint8_t v___y_4363_; lean_object* v_fst_4366_; lean_object* v_snd_4367_; lean_object* v_fst_4368_; lean_object* v_snd_4369_; uint8_t v___x_4370_; 
v_key_4360_ = lean_ctor_get(v___x_4359_, 0);
v_val_4361_ = lean_ctor_get(v___x_4359_, 1);
v_fst_4366_ = lean_ctor_get(v_x_4353_, 0);
v_snd_4367_ = lean_ctor_get(v_x_4353_, 1);
v_fst_4368_ = lean_ctor_get(v_key_4360_, 0);
v_snd_4369_ = lean_ctor_get(v_key_4360_, 1);
v___x_4370_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4366_, v_fst_4368_);
if (v___x_4370_ == 0)
{
v___y_4363_ = v___x_4370_;
goto v___jp_4362_;
}
else
{
uint8_t v___x_4371_; 
v___x_4371_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4367_, v_snd_4369_);
v___y_4363_ = v___x_4371_;
goto v___jp_4362_;
}
v___jp_4362_:
{
if (v___y_4363_ == 0)
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_box(0);
return v___x_4364_;
}
else
{
lean_object* v___x_4365_; 
lean_inc(v_val_4361_);
v___x_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4365_, 0, v_val_4361_);
return v___x_4365_;
}
}
}
case 1:
{
lean_object* v_node_4372_; size_t v___x_4373_; size_t v___x_4374_; 
v_node_4372_ = lean_ctor_get(v___x_4359_, 0);
v___x_4373_ = ((size_t)5ULL);
v___x_4374_ = lean_usize_shift_right(v_x_4352_, v___x_4373_);
v_x_4351_ = v_node_4372_;
v_x_4352_ = v___x_4374_;
goto _start;
}
default: 
{
lean_object* v___x_4376_; 
v___x_4376_ = lean_box(0);
return v___x_4376_;
}
}
}
else
{
lean_object* v_ks_4377_; lean_object* v_vs_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_ks_4377_ = lean_ctor_get(v_x_4351_, 0);
v_vs_4378_ = lean_ctor_get(v_x_4351_, 1);
v___x_4379_ = lean_unsigned_to_nat(0u);
v___x_4380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4377_, v_vs_4378_, v___x_4379_, v_x_4353_);
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4381_, lean_object* v_x_4382_, lean_object* v_x_4383_){
_start:
{
size_t v_x_2667__boxed_4384_; lean_object* v_res_4385_; 
v_x_2667__boxed_4384_ = lean_unbox_usize(v_x_4382_);
lean_dec(v_x_4382_);
v_res_4385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4381_, v_x_2667__boxed_4384_, v_x_4383_);
lean_dec_ref(v_x_4383_);
lean_dec_ref(v_x_4381_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4386_, lean_object* v_x_4387_){
_start:
{
lean_object* v_fst_4388_; lean_object* v_snd_4389_; uint64_t v___x_4390_; uint64_t v___x_4391_; uint64_t v___x_4392_; size_t v___x_4393_; lean_object* v___x_4394_; 
v_fst_4388_ = lean_ctor_get(v_x_4387_, 0);
v_snd_4389_ = lean_ctor_get(v_x_4387_, 1);
v___x_4390_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4388_);
v___x_4391_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4389_);
v___x_4392_ = lean_uint64_mix_hash(v___x_4390_, v___x_4391_);
v___x_4393_ = lean_uint64_to_usize(v___x_4392_);
v___x_4394_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4386_, v___x_4393_, v_x_4387_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4395_, lean_object* v_x_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4395_, v_x_4396_);
lean_dec_ref(v_x_4396_);
lean_dec_ref(v_x_4395_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4398_, lean_object* v_x_4399_, lean_object* v_x_4400_, lean_object* v_x_4401_){
_start:
{
lean_object* v_ks_4402_; lean_object* v_vs_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4432_; 
v_ks_4402_ = lean_ctor_get(v_x_4398_, 0);
v_vs_4403_ = lean_ctor_get(v_x_4398_, 1);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_x_4398_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4405_ = v_x_4398_;
v_isShared_4406_ = v_isSharedCheck_4432_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_vs_4403_);
lean_inc(v_ks_4402_);
lean_dec(v_x_4398_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4432_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
uint8_t v___y_4408_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4420_ = lean_array_get_size(v_ks_4402_);
v___x_4421_ = lean_nat_dec_lt(v_x_4399_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
lean_del_object(v___x_4405_);
lean_dec(v_x_4399_);
v___x_4422_ = lean_array_push(v_ks_4402_, v_x_4400_);
v___x_4423_ = lean_array_push(v_vs_4403_, v_x_4401_);
v___x_4424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4422_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
return v___x_4424_;
}
else
{
lean_object* v_fst_4425_; lean_object* v_snd_4426_; lean_object* v_k_x27_4427_; lean_object* v_fst_4428_; lean_object* v_snd_4429_; uint8_t v___x_4430_; 
v_fst_4425_ = lean_ctor_get(v_x_4400_, 0);
v_snd_4426_ = lean_ctor_get(v_x_4400_, 1);
v_k_x27_4427_ = lean_array_fget_borrowed(v_ks_4402_, v_x_4399_);
v_fst_4428_ = lean_ctor_get(v_k_x27_4427_, 0);
v_snd_4429_ = lean_ctor_get(v_k_x27_4427_, 1);
v___x_4430_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4425_, v_fst_4428_);
if (v___x_4430_ == 0)
{
v___y_4408_ = v___x_4430_;
goto v___jp_4407_;
}
else
{
uint8_t v___x_4431_; 
v___x_4431_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4426_, v_snd_4429_);
v___y_4408_ = v___x_4431_;
goto v___jp_4407_;
}
}
v___jp_4407_:
{
if (v___y_4408_ == 0)
{
lean_object* v___x_4410_; 
if (v_isShared_4406_ == 0)
{
v___x_4410_ = v___x_4405_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_ks_4402_);
lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_vs_4403_);
v___x_4410_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_unsigned_to_nat(1u);
v___x_4412_ = lean_nat_add(v_x_4399_, v___x_4411_);
lean_dec(v_x_4399_);
v_x_4398_ = v___x_4410_;
v_x_4399_ = v___x_4412_;
goto _start;
}
}
else
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4415_ = lean_array_fset(v_ks_4402_, v_x_4399_, v_x_4400_);
v___x_4416_ = lean_array_fset(v_vs_4403_, v_x_4399_, v_x_4401_);
lean_dec(v_x_4399_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 1, v___x_4416_);
lean_ctor_set(v___x_4405_, 0, v___x_4415_);
v___x_4418_ = v___x_4405_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4415_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4433_, lean_object* v_k_4434_, lean_object* v_v_4435_){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = lean_unsigned_to_nat(0u);
v___x_4437_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4433_, v___x_4436_, v_k_4434_, v_v_4435_);
return v___x_4437_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4439_, size_t v_x_4440_, size_t v_x_4441_, lean_object* v_x_4442_, lean_object* v_x_4443_){
_start:
{
if (lean_obj_tag(v_x_4439_) == 0)
{
lean_object* v_es_4444_; size_t v___x_4445_; size_t v___x_4446_; lean_object* v_j_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v_es_4444_ = lean_ctor_get(v_x_4439_, 0);
v___x_4445_ = ((size_t)31ULL);
v___x_4446_ = lean_usize_land(v_x_4440_, v___x_4445_);
v_j_4447_ = lean_usize_to_nat(v___x_4446_);
v___x_4448_ = lean_array_get_size(v_es_4444_);
v___x_4449_ = lean_nat_dec_lt(v_j_4447_, v___x_4448_);
if (v___x_4449_ == 0)
{
lean_dec(v_j_4447_);
lean_dec(v_x_4443_);
lean_dec_ref(v_x_4442_);
return v_x_4439_;
}
else
{
lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4495_; 
lean_inc_ref(v_es_4444_);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_x_4439_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v_x_4439_, 0);
lean_dec(v_unused_4496_);
v___x_4451_ = v_x_4439_;
v_isShared_4452_ = v_isSharedCheck_4495_;
goto v_resetjp_4450_;
}
else
{
lean_dec(v_x_4439_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4495_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v_v_4453_; lean_object* v___x_4454_; lean_object* v_xs_x27_4455_; lean_object* v___y_4457_; 
v_v_4453_ = lean_array_fget(v_es_4444_, v_j_4447_);
v___x_4454_ = lean_box(0);
v_xs_x27_4455_ = lean_array_fset(v_es_4444_, v_j_4447_, v___x_4454_);
switch(lean_obj_tag(v_v_4453_))
{
case 0:
{
lean_object* v_key_4462_; lean_object* v_val_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4480_; 
v_key_4462_ = lean_ctor_get(v_v_4453_, 0);
v_val_4463_ = lean_ctor_get(v_v_4453_, 1);
v_isSharedCheck_4480_ = !lean_is_exclusive(v_v_4453_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4465_ = v_v_4453_;
v_isShared_4466_ = v_isSharedCheck_4480_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_val_4463_);
lean_inc(v_key_4462_);
lean_dec(v_v_4453_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4480_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
uint8_t v___y_4468_; lean_object* v_fst_4474_; lean_object* v_snd_4475_; lean_object* v_fst_4476_; lean_object* v_snd_4477_; uint8_t v___x_4478_; 
v_fst_4474_ = lean_ctor_get(v_x_4442_, 0);
v_snd_4475_ = lean_ctor_get(v_x_4442_, 1);
v_fst_4476_ = lean_ctor_get(v_key_4462_, 0);
v_snd_4477_ = lean_ctor_get(v_key_4462_, 1);
v___x_4478_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4474_, v_fst_4476_);
if (v___x_4478_ == 0)
{
v___y_4468_ = v___x_4478_;
goto v___jp_4467_;
}
else
{
uint8_t v___x_4479_; 
v___x_4479_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4475_, v_snd_4477_);
v___y_4468_ = v___x_4479_;
goto v___jp_4467_;
}
v___jp_4467_:
{
if (v___y_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_del_object(v___x_4465_);
v___x_4469_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4462_, v_val_4463_, v_x_4442_, v_x_4443_);
v___x_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
v___y_4457_ = v___x_4470_;
goto v___jp_4456_;
}
else
{
lean_object* v___x_4472_; 
lean_dec(v_val_4463_);
lean_dec(v_key_4462_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 1, v_x_4443_);
lean_ctor_set(v___x_4465_, 0, v_x_4442_);
v___x_4472_ = v___x_4465_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_x_4442_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v_x_4443_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
v___y_4457_ = v___x_4472_;
goto v___jp_4456_;
}
}
}
}
}
case 1:
{
lean_object* v_node_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4493_; 
v_node_4481_ = lean_ctor_get(v_v_4453_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_v_4453_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4483_ = v_v_4453_;
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_node_4481_);
lean_dec(v_v_4453_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
size_t v___x_4485_; size_t v___x_4486_; size_t v___x_4487_; size_t v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4491_; 
v___x_4485_ = ((size_t)5ULL);
v___x_4486_ = lean_usize_shift_right(v_x_4440_, v___x_4485_);
v___x_4487_ = ((size_t)1ULL);
v___x_4488_ = lean_usize_add(v_x_4441_, v___x_4487_);
v___x_4489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4481_, v___x_4486_, v___x_4488_, v_x_4442_, v_x_4443_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4489_);
v___x_4491_ = v___x_4483_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
v___y_4457_ = v___x_4491_;
goto v___jp_4456_;
}
}
}
default: 
{
lean_object* v___x_4494_; 
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v_x_4442_);
lean_ctor_set(v___x_4494_, 1, v_x_4443_);
v___y_4457_ = v___x_4494_;
goto v___jp_4456_;
}
}
v___jp_4456_:
{
lean_object* v___x_4458_; lean_object* v___x_4460_; 
v___x_4458_ = lean_array_fset(v_xs_x27_4455_, v_j_4447_, v___y_4457_);
lean_dec(v_j_4447_);
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 0, v___x_4458_);
v___x_4460_ = v___x_4451_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4458_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
else
{
lean_object* v_ks_4497_; lean_object* v_vs_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4518_; 
v_ks_4497_ = lean_ctor_get(v_x_4439_, 0);
v_vs_4498_ = lean_ctor_get(v_x_4439_, 1);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_x_4439_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4500_ = v_x_4439_;
v_isShared_4501_ = v_isSharedCheck_4518_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_vs_4498_);
lean_inc(v_ks_4497_);
lean_dec(v_x_4439_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4518_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_ks_4497_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_vs_4498_);
v___x_4503_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v_newNode_4504_; uint8_t v___y_4506_; size_t v___x_4512_; uint8_t v___x_4513_; 
v_newNode_4504_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4503_, v_x_4442_, v_x_4443_);
v___x_4512_ = ((size_t)7ULL);
v___x_4513_ = lean_usize_dec_le(v___x_4512_, v_x_4441_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4514_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4504_);
v___x_4515_ = lean_unsigned_to_nat(4u);
v___x_4516_ = lean_nat_dec_lt(v___x_4514_, v___x_4515_);
lean_dec(v___x_4514_);
v___y_4506_ = v___x_4516_;
goto v___jp_4505_;
}
else
{
v___y_4506_ = v___x_4513_;
goto v___jp_4505_;
}
v___jp_4505_:
{
if (v___y_4506_ == 0)
{
lean_object* v_ks_4507_; lean_object* v_vs_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v_ks_4507_ = lean_ctor_get(v_newNode_4504_, 0);
lean_inc_ref(v_ks_4507_);
v_vs_4508_ = lean_ctor_get(v_newNode_4504_, 1);
lean_inc_ref(v_vs_4508_);
lean_dec_ref(v_newNode_4504_);
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4441_, v_ks_4507_, v_vs_4508_, v___x_4509_, v___x_4510_);
lean_dec_ref(v_vs_4508_);
lean_dec_ref(v_ks_4507_);
return v___x_4511_;
}
else
{
return v_newNode_4504_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4519_, lean_object* v_keys_4520_, lean_object* v_vals_4521_, lean_object* v_i_4522_, lean_object* v_entries_4523_){
_start:
{
lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4524_ = lean_array_get_size(v_keys_4520_);
v___x_4525_ = lean_nat_dec_lt(v_i_4522_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_dec(v_i_4522_);
return v_entries_4523_;
}
else
{
lean_object* v_k_4526_; lean_object* v_fst_4527_; lean_object* v_snd_4528_; lean_object* v_v_4529_; uint64_t v___x_4530_; uint64_t v___x_4531_; uint64_t v___x_4532_; size_t v_h_4533_; size_t v___x_4534_; lean_object* v___x_4535_; size_t v___x_4536_; size_t v___x_4537_; size_t v___x_4538_; size_t v_h_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v_k_4526_ = lean_array_fget_borrowed(v_keys_4520_, v_i_4522_);
v_fst_4527_ = lean_ctor_get(v_k_4526_, 0);
v_snd_4528_ = lean_ctor_get(v_k_4526_, 1);
v_v_4529_ = lean_array_fget_borrowed(v_vals_4521_, v_i_4522_);
v___x_4530_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4527_);
v___x_4531_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4528_);
v___x_4532_ = lean_uint64_mix_hash(v___x_4530_, v___x_4531_);
v_h_4533_ = lean_uint64_to_usize(v___x_4532_);
v___x_4534_ = ((size_t)5ULL);
v___x_4535_ = lean_unsigned_to_nat(1u);
v___x_4536_ = ((size_t)1ULL);
v___x_4537_ = lean_usize_sub(v_depth_4519_, v___x_4536_);
v___x_4538_ = lean_usize_mul(v___x_4534_, v___x_4537_);
v_h_4539_ = lean_usize_shift_right(v_h_4533_, v___x_4538_);
v___x_4540_ = lean_nat_add(v_i_4522_, v___x_4535_);
lean_dec(v_i_4522_);
lean_inc(v_v_4529_);
lean_inc(v_k_4526_);
v___x_4541_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4523_, v_h_4539_, v_depth_4519_, v_k_4526_, v_v_4529_);
v_i_4522_ = v___x_4540_;
v_entries_4523_ = v___x_4541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4543_, lean_object* v_keys_4544_, lean_object* v_vals_4545_, lean_object* v_i_4546_, lean_object* v_entries_4547_){
_start:
{
size_t v_depth_boxed_4548_; lean_object* v_res_4549_; 
v_depth_boxed_4548_ = lean_unbox_usize(v_depth_4543_);
lean_dec(v_depth_4543_);
v_res_4549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4548_, v_keys_4544_, v_vals_4545_, v_i_4546_, v_entries_4547_);
lean_dec_ref(v_vals_4545_);
lean_dec_ref(v_keys_4544_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4550_, lean_object* v_x_4551_, lean_object* v_x_4552_, lean_object* v_x_4553_, lean_object* v_x_4554_){
_start:
{
size_t v_x_2838__boxed_4555_; size_t v_x_2839__boxed_4556_; lean_object* v_res_4557_; 
v_x_2838__boxed_4555_ = lean_unbox_usize(v_x_4551_);
lean_dec(v_x_4551_);
v_x_2839__boxed_4556_ = lean_unbox_usize(v_x_4552_);
lean_dec(v_x_4552_);
v_res_4557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4550_, v_x_2838__boxed_4555_, v_x_2839__boxed_4556_, v_x_4553_, v_x_4554_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4558_, lean_object* v_x_4559_, lean_object* v_x_4560_){
_start:
{
lean_object* v_fst_4561_; lean_object* v_snd_4562_; uint64_t v___x_4563_; uint64_t v___x_4564_; uint64_t v___x_4565_; size_t v___x_4566_; size_t v___x_4567_; lean_object* v___x_4568_; 
v_fst_4561_ = lean_ctor_get(v_x_4559_, 0);
v_snd_4562_ = lean_ctor_get(v_x_4559_, 1);
v___x_4563_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4561_);
v___x_4564_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4562_);
v___x_4565_ = lean_uint64_mix_hash(v___x_4563_, v___x_4564_);
v___x_4566_ = lean_uint64_to_usize(v___x_4565_);
v___x_4567_ = ((size_t)1ULL);
v___x_4568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4558_, v___x_4566_, v___x_4567_, v_x_4559_, v_x_4560_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4569_, lean_object* v_t_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v___x_4577_; lean_object* v_defEqI_4578_; lean_object* v_key_4579_; lean_object* v___x_4580_; 
v___x_4577_ = lean_st_ref_get(v_a_4571_);
v_defEqI_4578_ = lean_ctor_get(v___x_4577_, 6);
lean_inc_ref(v_defEqI_4578_);
lean_dec(v___x_4577_);
lean_inc_ref(v_t_4570_);
lean_inc_ref(v_s_4569_);
v_key_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4579_, 0, v_s_4569_);
lean_ctor_set(v_key_4579_, 1, v_t_4570_);
v___x_4580_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4578_, v_key_4579_);
lean_dec_ref(v_defEqI_4578_);
if (lean_obj_tag(v___x_4580_) == 1)
{
lean_object* v_val_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
lean_dec_ref_known(v_key_4579_, 2);
lean_dec_ref(v_t_4570_);
lean_dec_ref(v_s_4569_);
v_val_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_val_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set_tag(v___x_4583_, 0);
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_val_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
else
{
lean_object* v___x_4589_; 
lean_dec(v___x_4580_);
v___x_4589_ = l_Lean_Meta_isDefEqI(v_s_4569_, v_t_4570_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4619_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4619_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4619_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v_share_4595_; lean_object* v_maxFVar_4596_; lean_object* v_proofInstInfo_4597_; lean_object* v_inferType_4598_; lean_object* v_getLevel_4599_; lean_object* v_congrInfo_4600_; lean_object* v_defEqI_4601_; lean_object* v_extensions_4602_; lean_object* v_issues_4603_; lean_object* v_canon_4604_; lean_object* v_instanceOverrides_4605_; uint8_t v_debug_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4618_; 
v___x_4594_ = lean_st_ref_take(v_a_4571_);
v_share_4595_ = lean_ctor_get(v___x_4594_, 0);
v_maxFVar_4596_ = lean_ctor_get(v___x_4594_, 1);
v_proofInstInfo_4597_ = lean_ctor_get(v___x_4594_, 2);
v_inferType_4598_ = lean_ctor_get(v___x_4594_, 3);
v_getLevel_4599_ = lean_ctor_get(v___x_4594_, 4);
v_congrInfo_4600_ = lean_ctor_get(v___x_4594_, 5);
v_defEqI_4601_ = lean_ctor_get(v___x_4594_, 6);
v_extensions_4602_ = lean_ctor_get(v___x_4594_, 7);
v_issues_4603_ = lean_ctor_get(v___x_4594_, 8);
v_canon_4604_ = lean_ctor_get(v___x_4594_, 9);
v_instanceOverrides_4605_ = lean_ctor_get(v___x_4594_, 10);
v_debug_4606_ = lean_ctor_get_uint8(v___x_4594_, sizeof(void*)*11);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4608_ = v___x_4594_;
v_isShared_4609_ = v_isSharedCheck_4618_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_instanceOverrides_4605_);
lean_inc(v_canon_4604_);
lean_inc(v_issues_4603_);
lean_inc(v_extensions_4602_);
lean_inc(v_defEqI_4601_);
lean_inc(v_congrInfo_4600_);
lean_inc(v_getLevel_4599_);
lean_inc(v_inferType_4598_);
lean_inc(v_proofInstInfo_4597_);
lean_inc(v_maxFVar_4596_);
lean_inc(v_share_4595_);
lean_dec(v___x_4594_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4618_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_inc(v_a_4590_);
v___x_4610_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4601_, v_key_4579_, v_a_4590_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 6, v___x_4610_);
v___x_4612_ = v___x_4608_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_share_4595_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v_maxFVar_4596_);
lean_ctor_set(v_reuseFailAlloc_4617_, 2, v_proofInstInfo_4597_);
lean_ctor_set(v_reuseFailAlloc_4617_, 3, v_inferType_4598_);
lean_ctor_set(v_reuseFailAlloc_4617_, 4, v_getLevel_4599_);
lean_ctor_set(v_reuseFailAlloc_4617_, 5, v_congrInfo_4600_);
lean_ctor_set(v_reuseFailAlloc_4617_, 6, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4617_, 7, v_extensions_4602_);
lean_ctor_set(v_reuseFailAlloc_4617_, 8, v_issues_4603_);
lean_ctor_set(v_reuseFailAlloc_4617_, 9, v_canon_4604_);
lean_ctor_set(v_reuseFailAlloc_4617_, 10, v_instanceOverrides_4605_);
lean_ctor_set_uint8(v_reuseFailAlloc_4617_, sizeof(void*)*11, v_debug_4606_);
v___x_4612_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4613_ = lean_st_ref_set(v_a_4571_, v___x_4612_);
if (v_isShared_4593_ == 0)
{
v___x_4615_ = v___x_4592_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4590_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4579_, 2);
return v___x_4589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4620_, lean_object* v_t_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4620_, v_t_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4629_, lean_object* v_t_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4629_, v_t_4630_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4639_, lean_object* v_t_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v_res_4648_; 
v_res_4648_ = l_Lean_Meta_Sym_isDefEqI(v_s_4639_, v_t_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4649_, lean_object* v_x_4650_, lean_object* v_x_4651_){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4650_, v_x_4651_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4653_, lean_object* v_x_4654_, lean_object* v_x_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4653_, v_x_4654_, v_x_4655_);
lean_dec_ref(v_x_4655_);
lean_dec_ref(v_x_4654_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4657_, lean_object* v_x_4658_, lean_object* v_x_4659_, lean_object* v_x_4660_){
_start:
{
lean_object* v___x_4661_; 
v___x_4661_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4658_, v_x_4659_, v_x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4662_, lean_object* v_x_4663_, size_t v_x_4664_, lean_object* v_x_4665_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4663_, v_x_4664_, v_x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4667_, lean_object* v_x_4668_, lean_object* v_x_4669_, lean_object* v_x_4670_){
_start:
{
size_t v_x_3117__boxed_4671_; lean_object* v_res_4672_; 
v_x_3117__boxed_4671_ = lean_unbox_usize(v_x_4669_);
lean_dec(v_x_4669_);
v_res_4672_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4667_, v_x_4668_, v_x_3117__boxed_4671_, v_x_4670_);
lean_dec_ref(v_x_4670_);
lean_dec_ref(v_x_4668_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4673_, lean_object* v_x_4674_, size_t v_x_4675_, size_t v_x_4676_, lean_object* v_x_4677_, lean_object* v_x_4678_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4674_, v_x_4675_, v_x_4676_, v_x_4677_, v_x_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4680_, lean_object* v_x_4681_, lean_object* v_x_4682_, lean_object* v_x_4683_, lean_object* v_x_4684_, lean_object* v_x_4685_){
_start:
{
size_t v_x_3128__boxed_4686_; size_t v_x_3129__boxed_4687_; lean_object* v_res_4688_; 
v_x_3128__boxed_4686_ = lean_unbox_usize(v_x_4682_);
lean_dec(v_x_4682_);
v_x_3129__boxed_4687_ = lean_unbox_usize(v_x_4683_);
lean_dec(v_x_4683_);
v_res_4688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4680_, v_x_4681_, v_x_3128__boxed_4686_, v_x_3129__boxed_4687_, v_x_4684_, v_x_4685_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4689_, lean_object* v_keys_4690_, lean_object* v_vals_4691_, lean_object* v_heq_4692_, lean_object* v_i_4693_, lean_object* v_k_4694_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4690_, v_vals_4691_, v_i_4693_, v_k_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4696_, lean_object* v_keys_4697_, lean_object* v_vals_4698_, lean_object* v_heq_4699_, lean_object* v_i_4700_, lean_object* v_k_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4696_, v_keys_4697_, v_vals_4698_, v_heq_4699_, v_i_4700_, v_k_4701_);
lean_dec_ref(v_k_4701_);
lean_dec_ref(v_vals_4698_);
lean_dec_ref(v_keys_4697_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4703_, lean_object* v_n_4704_, lean_object* v_k_4705_, lean_object* v_v_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4704_, v_k_4705_, v_v_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4708_, size_t v_depth_4709_, lean_object* v_keys_4710_, lean_object* v_vals_4711_, lean_object* v_heq_4712_, lean_object* v_i_4713_, lean_object* v_entries_4714_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4709_, v_keys_4710_, v_vals_4711_, v_i_4713_, v_entries_4714_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4716_, lean_object* v_depth_4717_, lean_object* v_keys_4718_, lean_object* v_vals_4719_, lean_object* v_heq_4720_, lean_object* v_i_4721_, lean_object* v_entries_4722_){
_start:
{
size_t v_depth_boxed_4723_; lean_object* v_res_4724_; 
v_depth_boxed_4723_ = lean_unbox_usize(v_depth_4717_);
lean_dec(v_depth_4717_);
v_res_4724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4716_, v_depth_boxed_4723_, v_keys_4718_, v_vals_4719_, v_heq_4720_, v_i_4721_, v_entries_4722_);
lean_dec_ref(v_vals_4719_);
lean_dec_ref(v_keys_4718_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4725_, lean_object* v_x_4726_, lean_object* v_x_4727_, lean_object* v_x_4728_, lean_object* v_x_4729_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4726_, v_x_4727_, v_x_4728_, v_x_4729_);
return v___x_4730_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___f_4732_; 
v___x_4731_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4732_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4732_, 0, v___x_4731_);
return v___f_4732_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_4733_; lean_object* v___f_4734_; 
v___x_4733_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4734_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4734_, 0, v___x_4733_);
return v___f_4734_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2(void){
_start:
{
lean_object* v___f_4735_; lean_object* v___f_4736_; lean_object* v___x_4737_; 
v___f_4735_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v___f_4736_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___f_4736_);
lean_ctor_set(v___x_4737_, 1, v___f_4735_);
return v___x_4737_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3(void){
_start:
{
lean_object* v___x_4738_; lean_object* v___f_4739_; 
v___x_4738_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4739_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4739_, 0, v___x_4738_);
return v___f_4739_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4(void){
_start:
{
lean_object* v___x_4740_; lean_object* v___f_4741_; 
v___x_4740_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4741_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4741_, 0, v___x_4740_);
return v___f_4741_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5(void){
_start:
{
lean_object* v___f_4742_; lean_object* v___f_4743_; lean_object* v___x_4744_; 
v___f_4742_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4);
v___f_4743_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3);
v___x_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4744_, 0, v___f_4743_);
lean_ctor_set(v___x_4744_, 1, v___f_4742_);
return v___x_4744_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___f_4746_; 
v___x_4745_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4746_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4746_, 0, v___x_4745_);
return v___f_4746_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_4747_; lean_object* v___f_4748_; 
v___x_4747_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4748_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4748_, 0, v___x_4747_);
return v___f_4748_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_4749_; lean_object* v___f_4750_; lean_object* v___x_4751_; 
v___f_4749_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_4750_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___f_4750_);
lean_ctor_set(v___x_4751_, 1, v___f_4749_);
return v___x_4751_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_4752_; lean_object* v___f_4753_; 
v___x_4752_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4753_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4753_, 0, v___x_4752_);
return v___f_4753_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___f_4755_; 
v___x_4754_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4755_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4755_, 0, v___x_4754_);
return v___f_4755_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; 
v___f_4756_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_4757_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___f_4757_);
lean_ctor_set(v___x_4758_, 1, v___f_4756_);
return v___x_4758_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4763_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4764_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4765_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4766_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4765_, v___x_4764_, v___x_4763_);
return v___x_4766_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___x_4767_; lean_object* v___f_4768_; lean_object* v___f_4769_; lean_object* v___x_4770_; 
v___x_4767_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_4768_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4769_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4770_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4769_, v___f_4768_, v___x_4767_);
return v___x_4770_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4771_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_4772_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4773_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4774_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4773_, v___x_4772_, v___x_4771_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___f_4776_; lean_object* v___f_4777_; lean_object* v___x_4778_; 
v___x_4775_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18);
v___f_4776_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4777_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4778_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4777_, v___f_4776_, v___x_4775_);
return v___x_4778_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20(void){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___f_4781_; 
v___x_4779_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4780_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4781_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4781_, 0, v___x_4780_);
lean_closure_set(v___f_4781_, 1, v___x_4779_);
return v___f_4781_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21(void){
_start:
{
lean_object* v___f_4782_; lean_object* v___f_4783_; lean_object* v___f_4784_; 
v___f_4782_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4783_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20);
v___f_4784_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4784_, 0, v___f_4783_);
lean_closure_set(v___f_4784_, 1, v___f_4782_);
return v___f_4784_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__22));
v___x_4787_ = l_Lean_stringToMessageData(v___x_4786_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4788_){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v_toApplicative_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4858_; 
v___x_4789_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4790_ = l_StateRefT_x27_instMonad___redArg(v___x_4789_);
v_toApplicative_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4858_ == 0)
{
lean_object* v_unused_4859_; 
v_unused_4859_ = lean_ctor_get(v___x_4790_, 1);
lean_dec(v_unused_4859_);
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4858_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_toApplicative_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4858_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_toFunctor_4795_; lean_object* v_toSeq_4796_; lean_object* v_toSeqLeft_4797_; lean_object* v_toSeqRight_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4856_; 
v_toFunctor_4795_ = lean_ctor_get(v_toApplicative_4791_, 0);
v_toSeq_4796_ = lean_ctor_get(v_toApplicative_4791_, 2);
v_toSeqLeft_4797_ = lean_ctor_get(v_toApplicative_4791_, 3);
v_toSeqRight_4798_ = lean_ctor_get(v_toApplicative_4791_, 4);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_toApplicative_4791_);
if (v_isSharedCheck_4856_ == 0)
{
lean_object* v_unused_4857_; 
v_unused_4857_ = lean_ctor_get(v_toApplicative_4791_, 1);
lean_dec(v_unused_4857_);
v___x_4800_ = v_toApplicative_4791_;
v_isShared_4801_ = v_isSharedCheck_4856_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_toSeqRight_4798_);
lean_inc(v_toSeqLeft_4797_);
lean_inc(v_toSeq_4796_);
lean_inc(v_toFunctor_4795_);
lean_dec(v_toApplicative_4791_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4856_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___f_4802_; lean_object* v___f_4803_; lean_object* v___f_4804_; lean_object* v___f_4805_; lean_object* v___x_4806_; lean_object* v___f_4807_; lean_object* v___f_4808_; lean_object* v___f_4809_; lean_object* v___x_4811_; 
v___f_4802_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4803_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4795_);
v___f_4804_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4804_, 0, v_toFunctor_4795_);
v___f_4805_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4805_, 0, v_toFunctor_4795_);
v___x_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___f_4804_);
lean_ctor_set(v___x_4806_, 1, v___f_4805_);
v___f_4807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4807_, 0, v_toSeqRight_4798_);
v___f_4808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4808_, 0, v_toSeqLeft_4797_);
v___f_4809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4809_, 0, v_toSeq_4796_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 4, v___f_4807_);
lean_ctor_set(v___x_4800_, 3, v___f_4808_);
lean_ctor_set(v___x_4800_, 2, v___f_4809_);
lean_ctor_set(v___x_4800_, 1, v___f_4802_);
lean_ctor_set(v___x_4800_, 0, v___x_4806_);
v___x_4811_ = v___x_4800_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4855_, 1, v___f_4802_);
lean_ctor_set(v_reuseFailAlloc_4855_, 2, v___f_4809_);
lean_ctor_set(v_reuseFailAlloc_4855_, 3, v___f_4808_);
lean_ctor_set(v_reuseFailAlloc_4855_, 4, v___f_4807_);
v___x_4811_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4813_; 
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 1, v___f_4803_);
lean_ctor_set(v___x_4793_, 0, v___x_4811_);
v___x_4813_ = v___x_4793_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4811_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___f_4803_);
v___x_4813_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4814_; lean_object* v_toApplicative_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4852_; 
v___x_4814_ = l_StateRefT_x27_instMonad___redArg(v___x_4813_);
v_toApplicative_4815_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4852_ == 0)
{
lean_object* v_unused_4853_; 
v_unused_4853_ = lean_ctor_get(v___x_4814_, 1);
lean_dec(v_unused_4853_);
v___x_4817_ = v___x_4814_;
v_isShared_4818_ = v_isSharedCheck_4852_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_toApplicative_4815_);
lean_dec(v___x_4814_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4852_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v_toFunctor_4819_; lean_object* v_toSeq_4820_; lean_object* v_toSeqLeft_4821_; lean_object* v_toSeqRight_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4850_; 
v_toFunctor_4819_ = lean_ctor_get(v_toApplicative_4815_, 0);
v_toSeq_4820_ = lean_ctor_get(v_toApplicative_4815_, 2);
v_toSeqLeft_4821_ = lean_ctor_get(v_toApplicative_4815_, 3);
v_toSeqRight_4822_ = lean_ctor_get(v_toApplicative_4815_, 4);
v_isSharedCheck_4850_ = !lean_is_exclusive(v_toApplicative_4815_);
if (v_isSharedCheck_4850_ == 0)
{
lean_object* v_unused_4851_; 
v_unused_4851_ = lean_ctor_get(v_toApplicative_4815_, 1);
lean_dec(v_unused_4851_);
v___x_4824_ = v_toApplicative_4815_;
v_isShared_4825_ = v_isSharedCheck_4850_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_toSeqRight_4822_);
lean_inc(v_toSeqLeft_4821_);
lean_inc(v_toSeq_4820_);
lean_inc(v_toFunctor_4819_);
lean_dec(v_toApplicative_4815_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4850_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___f_4826_; lean_object* v___f_4827_; lean_object* v___f_4828_; lean_object* v___f_4829_; lean_object* v___x_4830_; lean_object* v___f_4831_; lean_object* v___f_4832_; lean_object* v___f_4833_; lean_object* v___x_4835_; 
v___f_4826_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4827_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4819_);
v___f_4828_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4828_, 0, v_toFunctor_4819_);
v___f_4829_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4829_, 0, v_toFunctor_4819_);
v___x_4830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___f_4828_);
lean_ctor_set(v___x_4830_, 1, v___f_4829_);
v___f_4831_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4831_, 0, v_toSeqRight_4822_);
v___f_4832_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4832_, 0, v_toSeqLeft_4821_);
v___f_4833_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4833_, 0, v_toSeq_4820_);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 4, v___f_4831_);
lean_ctor_set(v___x_4824_, 3, v___f_4832_);
lean_ctor_set(v___x_4824_, 2, v___f_4833_);
lean_ctor_set(v___x_4824_, 1, v___f_4826_);
lean_ctor_set(v___x_4824_, 0, v___x_4830_);
v___x_4835_ = v___x_4824_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v___x_4830_);
lean_ctor_set(v_reuseFailAlloc_4849_, 1, v___f_4826_);
lean_ctor_set(v_reuseFailAlloc_4849_, 2, v___f_4833_);
lean_ctor_set(v_reuseFailAlloc_4849_, 3, v___f_4832_);
lean_ctor_set(v_reuseFailAlloc_4849_, 4, v___f_4831_);
v___x_4835_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
lean_object* v___x_4837_; 
if (v_isShared_4818_ == 0)
{
lean_ctor_set(v___x_4817_, 1, v___f_4827_);
lean_ctor_set(v___x_4817_, 0, v___x_4835_);
v___x_4837_ = v___x_4817_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4848_, 1, v___f_4827_);
v___x_4837_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v_toMonadRef_4842_; lean_object* v___f_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4838_ = l_StateRefT_x27_instMonad___redArg(v___x_4837_);
v___x_4839_ = l_ReaderT_instMonad___redArg(v___x_4838_);
v___x_4840_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___x_4841_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19);
v_toMonadRef_4842_ = lean_ctor_get(v___x_4841_, 0);
v___f_4843_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21);
lean_inc_ref(v___x_4839_);
v___x_4844_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4843_, v___x_4839_);
lean_inc_ref(v_toMonadRef_4842_);
v___x_4845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4840_);
lean_ctor_set(v___x_4845_, 1, v_toMonadRef_4842_);
lean_ctor_set(v___x_4845_, 2, v___x_4844_);
v___x_4846_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_4847_ = l_Lean_throwError___redArg(v___x_4839_, v___x_4845_, v___x_4846_);
return v___x_4847_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4860_, lean_object* v_extensions_4861_){
_start:
{
lean_object* v_id_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_id_4863_ = lean_ctor_get(v_ext_4860_, 0);
v___x_4864_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4865_ = lean_array_get_borrowed(v___x_4864_, v_extensions_4861_, v_id_4863_);
lean_inc(v___x_4865_);
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4867_, lean_object* v_extensions_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4867_, v_extensions_4868_);
lean_dec_ref(v_extensions_4868_);
lean_dec_ref(v_ext_4867_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_4871_, lean_object* v_ext_4872_, lean_object* v_extensions_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4872_, v_extensions_4873_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_4876_, lean_object* v_ext_4877_, lean_object* v_extensions_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_4876_, v_ext_4877_, v_extensions_4878_);
lean_dec_ref(v_extensions_4878_);
lean_dec_ref(v_ext_4877_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; lean_object* v_extensions_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_st_ref_get(v_a_4882_);
v_extensions_4886_ = lean_ctor_get(v___x_4885_, 7);
lean_inc_ref(v_extensions_4886_);
lean_dec(v___x_4885_);
v___x_4887_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4881_, v_extensions_4886_);
lean_dec_ref(v_extensions_4886_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4908_; 
v_a_4896_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4898_ = v___x_4887_;
v_isShared_4899_ = v_isSharedCheck_4908_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4887_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4908_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v_ref_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4906_; 
v_ref_4900_ = lean_ctor_get(v_a_4883_, 5);
v___x_4901_ = lean_io_error_to_string(v_a_4896_);
v___x_4902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
v___x_4903_ = l_Lean_MessageData_ofFormat(v___x_4902_);
lean_inc(v_ref_4900_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_ref_4900_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v___x_4904_);
v___x_4906_ = v___x_4898_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4909_, v_a_4910_, v_a_4911_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_ext_4909_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_4914_, lean_object* v_ext_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4915_, v_a_4917_, v_a_4920_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_4924_, lean_object* v_ext_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_4924_, v_ext_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
lean_dec_ref(v_ext_4925_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_4934_, lean_object* v_f_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v___x_4938_; lean_object* v_share_4939_; lean_object* v_maxFVar_4940_; lean_object* v_proofInstInfo_4941_; lean_object* v_inferType_4942_; lean_object* v_getLevel_4943_; lean_object* v_congrInfo_4944_; lean_object* v_defEqI_4945_; lean_object* v_extensions_4946_; lean_object* v_issues_4947_; lean_object* v_canon_4948_; lean_object* v_instanceOverrides_4949_; uint8_t v_debug_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4969_; 
v___x_4938_ = lean_st_ref_take(v_a_4936_);
v_share_4939_ = lean_ctor_get(v___x_4938_, 0);
v_maxFVar_4940_ = lean_ctor_get(v___x_4938_, 1);
v_proofInstInfo_4941_ = lean_ctor_get(v___x_4938_, 2);
v_inferType_4942_ = lean_ctor_get(v___x_4938_, 3);
v_getLevel_4943_ = lean_ctor_get(v___x_4938_, 4);
v_congrInfo_4944_ = lean_ctor_get(v___x_4938_, 5);
v_defEqI_4945_ = lean_ctor_get(v___x_4938_, 6);
v_extensions_4946_ = lean_ctor_get(v___x_4938_, 7);
v_issues_4947_ = lean_ctor_get(v___x_4938_, 8);
v_canon_4948_ = lean_ctor_get(v___x_4938_, 9);
v_instanceOverrides_4949_ = lean_ctor_get(v___x_4938_, 10);
v_debug_4950_ = lean_ctor_get_uint8(v___x_4938_, sizeof(void*)*11);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4952_ = v___x_4938_;
v_isShared_4953_ = v_isSharedCheck_4969_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_instanceOverrides_4949_);
lean_inc(v_canon_4948_);
lean_inc(v_issues_4947_);
lean_inc(v_extensions_4946_);
lean_inc(v_defEqI_4945_);
lean_inc(v_congrInfo_4944_);
lean_inc(v_getLevel_4943_);
lean_inc(v_inferType_4942_);
lean_inc(v_proofInstInfo_4941_);
lean_inc(v_maxFVar_4940_);
lean_inc(v_share_4939_);
lean_dec(v___x_4938_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4969_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v_id_4954_; lean_object* v___x_4955_; lean_object* v___y_4957_; lean_object* v___x_4963_; uint8_t v___x_4964_; 
v_id_4954_ = lean_ctor_get(v_ext_4934_, 0);
v___x_4955_ = lean_box(0);
v___x_4963_ = lean_array_get_size(v_extensions_4946_);
v___x_4964_ = lean_nat_dec_lt(v_id_4954_, v___x_4963_);
if (v___x_4964_ == 0)
{
lean_dec(v_f_4935_);
v___y_4957_ = v_extensions_4946_;
goto v___jp_4956_;
}
else
{
lean_object* v_v_4965_; lean_object* v_xs_x27_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_v_4965_ = lean_array_fget(v_extensions_4946_, v_id_4954_);
v_xs_x27_4966_ = lean_array_fset(v_extensions_4946_, v_id_4954_, v___x_4955_);
v___x_4967_ = lean_apply_1(v_f_4935_, v_v_4965_);
v___x_4968_ = lean_array_fset(v_xs_x27_4966_, v_id_4954_, v___x_4967_);
v___y_4957_ = v___x_4968_;
goto v___jp_4956_;
}
v___jp_4956_:
{
lean_object* v___x_4959_; 
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 7, v___y_4957_);
v___x_4959_ = v___x_4952_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_share_4939_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_maxFVar_4940_);
lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_proofInstInfo_4941_);
lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_inferType_4942_);
lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_getLevel_4943_);
lean_ctor_set(v_reuseFailAlloc_4962_, 5, v_congrInfo_4944_);
lean_ctor_set(v_reuseFailAlloc_4962_, 6, v_defEqI_4945_);
lean_ctor_set(v_reuseFailAlloc_4962_, 7, v___y_4957_);
lean_ctor_set(v_reuseFailAlloc_4962_, 8, v_issues_4947_);
lean_ctor_set(v_reuseFailAlloc_4962_, 9, v_canon_4948_);
lean_ctor_set(v_reuseFailAlloc_4962_, 10, v_instanceOverrides_4949_);
lean_ctor_set_uint8(v_reuseFailAlloc_4962_, sizeof(void*)*11, v_debug_4950_);
v___x_4959_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = lean_st_ref_set(v_a_4936_, v___x_4959_);
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4955_);
return v___x_4961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_4970_, lean_object* v_f_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4970_, v_f_4971_, v_a_4972_);
lean_dec(v_a_4972_);
lean_dec_ref(v_ext_4970_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_4975_, lean_object* v_ext_4976_, lean_object* v_f_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4976_, v_f_4977_, v_a_4979_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_4986_, lean_object* v_ext_4987_, lean_object* v_f_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_4986_, v_ext_4987_, v_f_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
lean_dec_ref(v_a_4989_);
lean_dec_ref(v_ext_4987_);
return v_res_4996_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
