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
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
v___x_187_ = lean_st_ref_set(v___x_181_, v___x_186_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
uint8_t v___x_440_; 
v___x_440_ = 0;
return v___x_440_;
}
else
{
lean_object* v_key_441_; lean_object* v_tail_442_; uint8_t v___x_443_; 
v_key_441_ = lean_ctor_get(v_x_439_, 0);
v_tail_442_ = lean_ctor_get(v_x_439_, 2);
v___x_443_ = l_Lean_ExprStructEq_beq(v_key_441_, v_a_438_);
if (v___x_443_ == 0)
{
v_x_439_ = v_tail_442_;
goto _start;
}
else
{
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_445_, v_x_446_);
lean_dec(v_x_446_);
lean_dec_ref(v_a_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
return v_x_449_;
}
else
{
lean_object* v_key_451_; lean_object* v_value_452_; lean_object* v_tail_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_476_; 
v_key_451_ = lean_ctor_get(v_x_450_, 0);
v_value_452_ = lean_ctor_get(v_x_450_, 1);
v_tail_453_ = lean_ctor_get(v_x_450_, 2);
v_isSharedCheck_476_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_476_ == 0)
{
v___x_455_ = v_x_450_;
v_isShared_456_ = v_isSharedCheck_476_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_tail_453_);
lean_inc(v_value_452_);
lean_inc(v_key_451_);
lean_dec(v_x_450_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_476_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v_fold_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_457_ = lean_array_get_size(v_x_449_);
v___x_458_ = l_Lean_ExprStructEq_hash(v_key_451_);
v___x_459_ = 32ULL;
v___x_460_ = lean_uint64_shift_right(v___x_458_, v___x_459_);
v_fold_461_ = lean_uint64_xor(v___x_458_, v___x_460_);
v___x_462_ = 16ULL;
v___x_463_ = lean_uint64_shift_right(v_fold_461_, v___x_462_);
v___x_464_ = lean_uint64_xor(v_fold_461_, v___x_463_);
v___x_465_ = lean_uint64_to_usize(v___x_464_);
v___x_466_ = lean_usize_of_nat(v___x_457_);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_sub(v___x_466_, v___x_467_);
v___x_469_ = lean_usize_land(v___x_465_, v___x_468_);
v___x_470_ = lean_array_uget_borrowed(v_x_449_, v___x_469_);
lean_inc(v___x_470_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 2, v___x_470_);
v___x_472_ = v___x_455_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_key_451_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_value_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v___x_470_);
v___x_472_ = v_reuseFailAlloc_475_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; 
v___x_473_ = lean_array_uset(v_x_449_, v___x_469_, v___x_472_);
v_x_449_ = v___x_473_;
v_x_450_ = v_tail_453_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_477_, lean_object* v_source_478_, lean_object* v_target_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_array_get_size(v_source_478_);
v___x_481_ = lean_nat_dec_lt(v_i_477_, v___x_480_);
if (v___x_481_ == 0)
{
lean_dec_ref(v_source_478_);
lean_dec(v_i_477_);
return v_target_479_;
}
else
{
lean_object* v_es_482_; lean_object* v___x_483_; lean_object* v_source_484_; lean_object* v_target_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_es_482_ = lean_array_fget(v_source_478_, v_i_477_);
v___x_483_ = lean_box(0);
v_source_484_ = lean_array_fset(v_source_478_, v_i_477_, v___x_483_);
v_target_485_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_479_, v_es_482_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_i_477_, v___x_486_);
lean_dec(v_i_477_);
v_i_477_ = v___x_487_;
v_source_478_ = v_source_484_;
v_target_479_ = v_target_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_nbuckets_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_490_ = lean_array_get_size(v_data_489_);
v___x_491_ = lean_unsigned_to_nat(2u);
v_nbuckets_492_ = lean_nat_mul(v___x_490_, v___x_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_box(0);
v___x_495_ = lean_mk_array(v_nbuckets_492_, v___x_494_);
v___x_496_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_493_, v_data_489_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_dec(v_b_498_);
lean_dec_ref(v_a_497_);
return v_x_499_;
}
else
{
lean_object* v_key_500_; lean_object* v_value_501_; lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_514_; 
v_key_500_ = lean_ctor_get(v_x_499_, 0);
v_value_501_ = lean_ctor_get(v_x_499_, 1);
v_tail_502_ = lean_ctor_get(v_x_499_, 2);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_514_ == 0)
{
v___x_504_ = v_x_499_;
v_isShared_505_ = v_isSharedCheck_514_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_inc(v_value_501_);
lean_inc(v_key_500_);
lean_dec(v_x_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_514_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; 
v___x_506_ = l_Lean_ExprStructEq_beq(v_key_500_, v_a_497_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_497_, v_b_498_, v_tail_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 2, v___x_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_key_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_value_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v_value_501_);
lean_dec(v_key_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_b_498_);
lean_ctor_set(v___x_504_, 0, v_a_497_);
v___x_512_ = v___x_504_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_b_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_tail_502_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v_size_518_; lean_object* v_buckets_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_562_; 
v_size_518_ = lean_ctor_get(v_m_515_, 0);
v_buckets_519_ = lean_ctor_get(v_m_515_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_m_515_);
if (v_isSharedCheck_562_ == 0)
{
v___x_521_ = v_m_515_;
v_isShared_522_ = v_isSharedCheck_562_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_buckets_519_);
lean_inc(v_size_518_);
lean_dec(v_m_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_562_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v___x_526_; uint64_t v_fold_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v_bkt_536_; uint8_t v___x_537_; 
v___x_523_ = lean_array_get_size(v_buckets_519_);
v___x_524_ = l_Lean_ExprStructEq_hash(v_a_516_);
v___x_525_ = 32ULL;
v___x_526_ = lean_uint64_shift_right(v___x_524_, v___x_525_);
v_fold_527_ = lean_uint64_xor(v___x_524_, v___x_526_);
v___x_528_ = 16ULL;
v___x_529_ = lean_uint64_shift_right(v_fold_527_, v___x_528_);
v___x_530_ = lean_uint64_xor(v_fold_527_, v___x_529_);
v___x_531_ = lean_uint64_to_usize(v___x_530_);
v___x_532_ = lean_usize_of_nat(v___x_523_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_usize_land(v___x_531_, v___x_534_);
v_bkt_536_ = lean_array_uget_borrowed(v_buckets_519_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_516_, v_bkt_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v_size_x27_539_; lean_object* v___x_540_; lean_object* v_buckets_x27_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v_size_x27_539_ = lean_nat_add(v_size_518_, v___x_538_);
lean_dec(v_size_518_);
lean_inc(v_bkt_536_);
v___x_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_540_, 0, v_a_516_);
lean_ctor_set(v___x_540_, 1, v_b_517_);
lean_ctor_set(v___x_540_, 2, v_bkt_536_);
v_buckets_x27_541_ = lean_array_uset(v_buckets_519_, v___x_535_, v___x_540_);
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_nat_mul(v_size_x27_539_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(3u);
v___x_545_ = lean_nat_div(v___x_543_, v___x_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_array_get_size(v_buckets_x27_541_);
v___x_547_ = lean_nat_dec_le(v___x_545_, v___x_546_);
lean_dec(v___x_545_);
if (v___x_547_ == 0)
{
lean_object* v_val_548_; lean_object* v___x_550_; 
v_val_548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_541_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_val_548_);
lean_ctor_set(v___x_521_, 0, v_size_x27_539_);
v___x_550_ = v___x_521_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_size_x27_539_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_val_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v___x_553_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_buckets_x27_541_);
lean_ctor_set(v___x_521_, 0, v_size_x27_539_);
v___x_553_ = v___x_521_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_size_x27_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_buckets_x27_541_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v___x_555_; lean_object* v_buckets_x27_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
lean_inc(v_bkt_536_);
v___x_555_ = lean_box(0);
v_buckets_x27_556_ = lean_array_uset(v_buckets_519_, v___x_535_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_516_, v_b_517_, v_bkt_536_);
v___x_558_ = lean_array_uset(v_buckets_x27_556_, v___x_535_, v___x_557_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_558_);
v___x_560_ = v___x_521_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_size_518_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_563_, lean_object* v_e_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_st_ref_take(v_a_563_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_567_, v_e_564_, v_a_565_);
v___x_569_ = lean_st_ref_set(v_a_563_, v___x_568_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_571_, lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_571_, v_e_572_, v_a_573_);
lean_dec(v_a_571_);
return v_res_575_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = l_Lean_maxRecDepthErrorMessage;
v___x_582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_584_ = l_Lean_MessageData_ofFormat(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_586_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_587_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_ref_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___y_604_; lean_object* v_fileName_613_; lean_object* v_fileMap_614_; lean_object* v_options_615_; lean_object* v_currRecDepth_616_; lean_object* v_maxRecDepth_617_; lean_object* v_ref_618_; lean_object* v_currNamespace_619_; lean_object* v_openDecls_620_; lean_object* v_initHeartbeats_621_; lean_object* v_maxHeartbeats_622_; lean_object* v_quotContext_623_; lean_object* v_currMacroScope_624_; uint8_t v_diag_625_; lean_object* v_cancelTk_x3f_626_; uint8_t v_suppressElabErrors_627_; lean_object* v_inheritedTraceOptions_628_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_fileName_613_ = lean_ctor_get(v___y_600_, 0);
v_fileMap_614_ = lean_ctor_get(v___y_600_, 1);
v_options_615_ = lean_ctor_get(v___y_600_, 2);
v_currRecDepth_616_ = lean_ctor_get(v___y_600_, 3);
v_maxRecDepth_617_ = lean_ctor_get(v___y_600_, 4);
v_ref_618_ = lean_ctor_get(v___y_600_, 5);
v_currNamespace_619_ = lean_ctor_get(v___y_600_, 6);
v_openDecls_620_ = lean_ctor_get(v___y_600_, 7);
v_initHeartbeats_621_ = lean_ctor_get(v___y_600_, 8);
v_maxHeartbeats_622_ = lean_ctor_get(v___y_600_, 9);
v_quotContext_623_ = lean_ctor_get(v___y_600_, 10);
v_currMacroScope_624_ = lean_ctor_get(v___y_600_, 11);
v_diag_625_ = lean_ctor_get_uint8(v___y_600_, sizeof(void*)*14);
v_cancelTk_x3f_626_ = lean_ctor_get(v___y_600_, 12);
v_suppressElabErrors_627_ = lean_ctor_get_uint8(v___y_600_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_628_ = lean_ctor_get(v___y_600_, 13);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_nat_dec_eq(v_maxRecDepth_617_, v___x_634_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_eq(v_currRecDepth_616_, v_maxRecDepth_617_);
if (v___x_636_ == 0)
{
goto v___jp_629_;
}
else
{
lean_object* v___x_637_; 
lean_dec_ref(v_x_596_);
lean_inc(v_ref_618_);
v___x_637_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_618_);
v___y_604_ = v___x_637_;
goto v___jp_603_;
}
}
else
{
goto v___jp_629_;
}
v___jp_603_:
{
if (lean_obj_tag(v___y_604_) == 0)
{
return v___y_604_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___y_604_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___y_604_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___y_604_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___y_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
v___jp_629_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_currRecDepth_616_, v___x_630_);
lean_inc_ref(v_inheritedTraceOptions_628_);
lean_inc(v_cancelTk_x3f_626_);
lean_inc(v_currMacroScope_624_);
lean_inc(v_quotContext_623_);
lean_inc(v_maxHeartbeats_622_);
lean_inc(v_initHeartbeats_621_);
lean_inc(v_openDecls_620_);
lean_inc(v_currNamespace_619_);
lean_inc(v_ref_618_);
lean_inc(v_maxRecDepth_617_);
lean_inc_ref(v_options_615_);
lean_inc_ref(v_fileMap_614_);
lean_inc_ref(v_fileName_613_);
v___x_632_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_632_, 0, v_fileName_613_);
lean_ctor_set(v___x_632_, 1, v_fileMap_614_);
lean_ctor_set(v___x_632_, 2, v_options_615_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
lean_ctor_set(v___x_632_, 4, v_maxRecDepth_617_);
lean_ctor_set(v___x_632_, 5, v_ref_618_);
lean_ctor_set(v___x_632_, 6, v_currNamespace_619_);
lean_ctor_set(v___x_632_, 7, v_openDecls_620_);
lean_ctor_set(v___x_632_, 8, v_initHeartbeats_621_);
lean_ctor_set(v___x_632_, 9, v_maxHeartbeats_622_);
lean_ctor_set(v___x_632_, 10, v_quotContext_623_);
lean_ctor_set(v___x_632_, 11, v_currMacroScope_624_);
lean_ctor_set(v___x_632_, 12, v_cancelTk_x3f_626_);
lean_ctor_set(v___x_632_, 13, v_inheritedTraceOptions_628_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*14, v_diag_625_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*14 + 1, v_suppressElabErrors_627_);
lean_inc(v___y_601_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
v___x_633_ = lean_apply_6(v_x_596_, v___y_597_, v___y_598_, v___y_599_, v___x_632_, v___y_601_, lean_box(0));
v___y_604_ = v___x_633_;
goto v___jp_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_646_, lean_object* v_x_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_apply_1(v_x_647_, lean_box(0));
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_655_, lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_655_, v_x_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_664_) == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_box(0);
return v___x_665_;
}
else
{
lean_object* v_key_666_; lean_object* v_value_667_; lean_object* v_tail_668_; uint8_t v___x_669_; 
v_key_666_ = lean_ctor_get(v_x_664_, 0);
v_value_667_ = lean_ctor_get(v_x_664_, 1);
v_tail_668_ = lean_ctor_get(v_x_664_, 2);
v___x_669_ = l_Lean_ExprStructEq_beq(v_key_666_, v_a_663_);
if (v___x_669_ == 0)
{
v_x_664_ = v_tail_668_;
goto _start;
}
else
{
lean_object* v___x_671_; 
lean_inc(v_value_667_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_value_667_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_672_, lean_object* v_x_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec_ref(v_a_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_buckets_677_; lean_object* v___x_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v_fold_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_buckets_677_ = lean_ctor_get(v_m_675_, 1);
v___x_678_ = lean_array_get_size(v_buckets_677_);
v___x_679_ = l_Lean_ExprStructEq_hash(v_a_676_);
v___x_680_ = 32ULL;
v___x_681_ = lean_uint64_shift_right(v___x_679_, v___x_680_);
v_fold_682_ = lean_uint64_xor(v___x_679_, v___x_681_);
v___x_683_ = 16ULL;
v___x_684_ = lean_uint64_shift_right(v_fold_682_, v___x_683_);
v___x_685_ = lean_uint64_xor(v_fold_682_, v___x_684_);
v___x_686_ = lean_uint64_to_usize(v___x_685_);
v___x_687_ = lean_usize_of_nat(v___x_678_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_sub(v___x_687_, v___x_688_);
v___x_690_ = lean_usize_land(v___x_686_, v___x_689_);
v___x_691_ = lean_array_uget_borrowed(v_buckets_677_, v___x_690_);
v___x_692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_676_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_693_, v_a_694_);
lean_dec_ref(v_a_694_);
lean_dec_ref(v_m_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_696_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_710_, lean_object* v___y_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_711_);
v___x_718_ = lean_apply_7(v_k_710_, v_b_712_, v___y_711_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, lean_box(0));
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_719_, lean_object* v___y_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_719_, v___y_720_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_720_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_728_, uint8_t v_bi_729_, lean_object* v_type_730_, lean_object* v_k_731_, uint8_t v_kind_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; 
lean_inc(v___y_733_);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_739_, 0, v_k_731_);
lean_closure_set(v___f_739_, 1, v___y_733_);
v___x_740_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_728_, v_bi_729_, v_type_730_, v___f_739_, v_kind_732_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_740_) == 0)
{
return v___x_740_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_749_, lean_object* v_bi_750_, lean_object* v_type_751_, lean_object* v_k_752_, lean_object* v_kind_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v_bi_boxed_760_; uint8_t v_kind_boxed_761_; lean_object* v_res_762_; 
v_bi_boxed_760_ = lean_unbox(v_bi_750_);
v_kind_boxed_761_ = lean_unbox(v_kind_753_);
v_res_762_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_749_, v_bi_boxed_760_, v_type_751_, v_k_752_, v_kind_boxed_761_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_763_, lean_object* v_type_764_, lean_object* v_val_765_, lean_object* v_k_766_, uint8_t v_nondep_767_, uint8_t v_kind_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___f_775_; lean_object* v___x_776_; 
lean_inc(v___y_769_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_775_, 0, v_k_766_);
lean_closure_set(v___f_775_, 1, v___y_769_);
v___x_776_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_763_, v_type_764_, v_val_765_, v___f_775_, v_nondep_767_, v_kind_768_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
if (lean_obj_tag(v___x_776_) == 0)
{
return v___x_776_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_785_, lean_object* v_type_786_, lean_object* v_val_787_, lean_object* v_k_788_, lean_object* v_nondep_789_, lean_object* v_kind_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
uint8_t v_nondep_boxed_797_; uint8_t v_kind_boxed_798_; lean_object* v_res_799_; 
v_nondep_boxed_797_ = lean_unbox(v_nondep_789_);
v_kind_boxed_798_ = lean_unbox(v_kind_790_);
v_res_799_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_785_, v_type_786_, v_val_787_, v_k_788_, v_nondep_boxed_797_, v_kind_boxed_798_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_803_, lean_object* v_pre_804_, lean_object* v_post_805_, uint8_t v_usedLetOnly_806_, uint8_t v_skipConstInApp_807_, uint8_t v_skipInstances_808_, lean_object* v_body_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_array_push(v_fvars_803_, v_x_810_);
v___x_818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_804_, v_post_805_, v_usedLetOnly_806_, v_skipConstInApp_807_, v_skipInstances_808_, v___x_817_, v_body_809_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_819_, lean_object* v_pre_820_, lean_object* v_post_821_, lean_object* v_usedLetOnly_822_, lean_object* v_skipConstInApp_823_, lean_object* v_skipInstances_824_, lean_object* v_body_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v_usedLetOnly_boxed_833_; uint8_t v_skipConstInApp_boxed_834_; uint8_t v_skipInstances_boxed_835_; lean_object* v_res_836_; 
v_usedLetOnly_boxed_833_ = lean_unbox(v_usedLetOnly_822_);
v_skipConstInApp_boxed_834_ = lean_unbox(v_skipConstInApp_823_);
v_skipInstances_boxed_835_ = lean_unbox(v_skipInstances_824_);
v_res_836_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_819_, v_pre_820_, v_post_821_, v_usedLetOnly_boxed_833_, v_skipConstInApp_boxed_834_, v_skipInstances_boxed_835_, v_body_825_, v_x_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_837_, lean_object* v_post_838_, uint8_t v_usedLetOnly_839_, uint8_t v_skipConstInApp_840_, uint8_t v_skipInstances_841_, lean_object* v_e_842_, lean_object* v_a_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
lean_inc_ref(v_post_838_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc_ref(v_e_842_);
v___x_849_ = lean_apply_6(v_post_838_, v_e_842_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, lean_box(0));
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_868_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
switch(lean_obj_tag(v_a_850_))
{
case 0:
{
lean_object* v_e_854_; lean_object* v___x_856_; 
lean_dec_ref(v_e_842_);
lean_dec_ref(v_post_838_);
lean_dec_ref(v_pre_837_);
v_e_854_ = lean_ctor_get(v_a_850_, 0);
lean_inc_ref(v_e_854_);
lean_dec_ref_known(v_a_850_, 1);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_e_854_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_e_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
case 1:
{
lean_object* v_e_858_; lean_object* v___x_859_; 
lean_del_object(v___x_852_);
lean_dec_ref(v_e_842_);
v_e_858_ = lean_ctor_get(v_a_850_, 0);
lean_inc_ref(v_e_858_);
lean_dec_ref_known(v_a_850_, 1);
v___x_859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_837_, v_post_838_, v_usedLetOnly_839_, v_skipConstInApp_840_, v_skipInstances_841_, v_e_858_, v_a_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
return v___x_859_;
}
default: 
{
lean_object* v_e_x3f_860_; 
lean_dec_ref(v_post_838_);
lean_dec_ref(v_pre_837_);
v_e_x3f_860_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_e_x3f_860_);
lean_dec_ref_known(v_a_850_, 1);
if (lean_obj_tag(v_e_x3f_860_) == 0)
{
lean_object* v___x_862_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_e_842_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_e_842_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v_val_864_; lean_object* v___x_866_; 
lean_dec_ref(v_e_842_);
v_val_864_ = lean_ctor_get(v_e_x3f_860_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v_e_x3f_860_, 1);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_val_864_);
v___x_866_ = v___x_852_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_val_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v_e_842_);
lean_dec_ref(v_post_838_);
lean_dec_ref(v_pre_837_);
v_a_869_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_849_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_849_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_877_, lean_object* v_post_878_, uint8_t v_usedLetOnly_879_, uint8_t v_skipConstInApp_880_, uint8_t v_skipInstances_881_, lean_object* v_fvars_882_, lean_object* v_e_883_, lean_object* v_a_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
if (lean_obj_tag(v_e_883_) == 6)
{
lean_object* v_binderName_890_; lean_object* v_binderType_891_; lean_object* v_body_892_; uint8_t v_binderInfo_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_binderName_890_ = lean_ctor_get(v_e_883_, 0);
lean_inc(v_binderName_890_);
v_binderType_891_ = lean_ctor_get(v_e_883_, 1);
lean_inc_ref(v_binderType_891_);
v_body_892_ = lean_ctor_get(v_e_883_, 2);
lean_inc_ref(v_body_892_);
v_binderInfo_893_ = lean_ctor_get_uint8(v_e_883_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_883_, 3);
v___x_894_ = lean_expr_instantiate_rev(v_binderType_891_, v_fvars_882_);
lean_dec_ref(v_binderType_891_);
lean_inc_ref(v_post_878_);
lean_inc_ref(v_pre_877_);
v___x_895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_877_, v_post_878_, v_usedLetOnly_879_, v_skipConstInApp_880_, v_skipInstances_881_, v___x_894_, v_a_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___f_900_; uint8_t v___x_901_; lean_object* v___x_902_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_box(v_usedLetOnly_879_);
v___x_898_ = lean_box(v_skipConstInApp_880_);
v___x_899_ = lean_box(v_skipInstances_881_);
v___f_900_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_900_, 0, v_fvars_882_);
lean_closure_set(v___f_900_, 1, v_pre_877_);
lean_closure_set(v___f_900_, 2, v_post_878_);
lean_closure_set(v___f_900_, 3, v___x_897_);
lean_closure_set(v___f_900_, 4, v___x_898_);
lean_closure_set(v___f_900_, 5, v___x_899_);
lean_closure_set(v___f_900_, 6, v_body_892_);
v___x_901_ = 0;
v___x_902_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_890_, v_binderInfo_893_, v_a_896_, v___f_900_, v___x_901_, v_a_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_902_;
}
else
{
lean_dec_ref(v_body_892_);
lean_dec(v_binderName_890_);
lean_dec_ref(v_fvars_882_);
lean_dec_ref(v_post_878_);
lean_dec_ref(v_pre_877_);
return v___x_895_;
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_expr_instantiate_rev(v_e_883_, v_fvars_882_);
lean_dec_ref(v_e_883_);
lean_inc_ref(v_post_878_);
lean_inc_ref(v_pre_877_);
v___x_904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_877_, v_post_878_, v_usedLetOnly_879_, v_skipConstInApp_880_, v_skipInstances_881_, v___x_903_, v_a_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = 0;
v___x_907_ = 1;
v___x_908_ = 1;
v___x_909_ = l_Lean_Meta_mkLambdaFVars(v_fvars_882_, v_a_905_, v___x_906_, v_usedLetOnly_879_, v___x_906_, v___x_907_, v___x_908_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec_ref(v_fvars_882_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_877_, v_post_878_, v_usedLetOnly_879_, v_skipConstInApp_880_, v_skipInstances_881_, v_a_910_, v_a_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_911_;
}
else
{
lean_dec_ref(v_post_878_);
lean_dec_ref(v_pre_877_);
return v___x_909_;
}
}
else
{
lean_dec_ref(v_fvars_882_);
lean_dec_ref(v_post_878_);
lean_dec_ref(v_pre_877_);
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_912_, lean_object* v_pre_913_, lean_object* v_post_914_, uint8_t v_usedLetOnly_915_, uint8_t v_skipConstInApp_916_, uint8_t v_skipInstances_917_, lean_object* v_body_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_array_push(v_fvars_912_, v_x_919_);
v___x_927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v___x_926_, v_body_918_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_928_, lean_object* v_pre_929_, lean_object* v_post_930_, lean_object* v_usedLetOnly_931_, lean_object* v_skipConstInApp_932_, lean_object* v_skipInstances_933_, lean_object* v_body_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v_usedLetOnly_boxed_942_; uint8_t v_skipConstInApp_boxed_943_; uint8_t v_skipInstances_boxed_944_; lean_object* v_res_945_; 
v_usedLetOnly_boxed_942_ = lean_unbox(v_usedLetOnly_931_);
v_skipConstInApp_boxed_943_ = lean_unbox(v_skipConstInApp_932_);
v_skipInstances_boxed_944_ = lean_unbox(v_skipInstances_933_);
v_res_945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_928_, v_pre_929_, v_post_930_, v_usedLetOnly_boxed_942_, v_skipConstInApp_boxed_943_, v_skipInstances_boxed_944_, v_body_934_, v_x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_946_, lean_object* v_post_947_, uint8_t v_usedLetOnly_948_, uint8_t v_skipConstInApp_949_, uint8_t v_skipInstances_950_, lean_object* v_fvars_951_, lean_object* v_e_952_, lean_object* v_a_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
if (lean_obj_tag(v_e_952_) == 8)
{
lean_object* v_declName_959_; lean_object* v_type_960_; lean_object* v_value_961_; lean_object* v_body_962_; uint8_t v_nondep_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_declName_959_ = lean_ctor_get(v_e_952_, 0);
lean_inc(v_declName_959_);
v_type_960_ = lean_ctor_get(v_e_952_, 1);
lean_inc_ref(v_type_960_);
v_value_961_ = lean_ctor_get(v_e_952_, 2);
lean_inc_ref(v_value_961_);
v_body_962_ = lean_ctor_get(v_e_952_, 3);
lean_inc_ref(v_body_962_);
v_nondep_963_ = lean_ctor_get_uint8(v_e_952_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_952_, 4);
v___x_964_ = lean_expr_instantiate_rev(v_type_960_, v_fvars_951_);
lean_dec_ref(v_type_960_);
lean_inc_ref(v_post_947_);
lean_inc_ref(v_pre_946_);
v___x_965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_946_, v_post_947_, v_usedLetOnly_948_, v_skipConstInApp_949_, v_skipInstances_950_, v___x_964_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = lean_expr_instantiate_rev(v_value_961_, v_fvars_951_);
lean_dec_ref(v_value_961_);
lean_inc_ref(v_post_947_);
lean_inc_ref(v_pre_946_);
v___x_968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_946_, v_post_947_, v_usedLetOnly_948_, v_skipConstInApp_949_, v_skipInstances_950_, v___x_967_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___f_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = lean_box(v_usedLetOnly_948_);
v___x_971_ = lean_box(v_skipConstInApp_949_);
v___x_972_ = lean_box(v_skipInstances_950_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_973_, 0, v_fvars_951_);
lean_closure_set(v___f_973_, 1, v_pre_946_);
lean_closure_set(v___f_973_, 2, v_post_947_);
lean_closure_set(v___f_973_, 3, v___x_970_);
lean_closure_set(v___f_973_, 4, v___x_971_);
lean_closure_set(v___f_973_, 5, v___x_972_);
lean_closure_set(v___f_973_, 6, v_body_962_);
v___x_974_ = 0;
v___x_975_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_959_, v_a_966_, v_a_969_, v___f_973_, v_nondep_963_, v___x_974_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_975_;
}
else
{
lean_dec(v_a_966_);
lean_dec_ref(v_body_962_);
lean_dec(v_declName_959_);
lean_dec_ref(v_fvars_951_);
lean_dec_ref(v_post_947_);
lean_dec_ref(v_pre_946_);
return v___x_968_;
}
}
else
{
lean_dec_ref(v_body_962_);
lean_dec_ref(v_value_961_);
lean_dec(v_declName_959_);
lean_dec_ref(v_fvars_951_);
lean_dec_ref(v_post_947_);
lean_dec_ref(v_pre_946_);
return v___x_965_;
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_expr_instantiate_rev(v_e_952_, v_fvars_951_);
lean_dec_ref(v_e_952_);
lean_inc_ref(v_post_947_);
lean_inc_ref(v_pre_946_);
v___x_977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_946_, v_post_947_, v_usedLetOnly_948_, v_skipConstInApp_949_, v_skipInstances_950_, v___x_976_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; uint8_t v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = 0;
v___x_980_ = 1;
v___x_981_ = l_Lean_Meta_mkLetFVars(v_fvars_951_, v_a_978_, v_usedLetOnly_948_, v___x_979_, v___x_980_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec_ref(v_fvars_951_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_946_, v_post_947_, v_usedLetOnly_948_, v_skipConstInApp_949_, v_skipInstances_950_, v_a_982_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_983_;
}
else
{
lean_dec_ref(v_post_947_);
lean_dec_ref(v_pre_946_);
return v___x_981_;
}
}
else
{
lean_dec_ref(v_fvars_951_);
lean_dec_ref(v_post_947_);
lean_dec_ref(v_pre_946_);
return v___x_977_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v_dummy_985_; 
v___x_984_ = lean_box(0);
v_dummy_985_ = l_Lean_Expr_sort___override(v___x_984_);
return v_dummy_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_986_, lean_object* v_post_987_, uint8_t v_usedLetOnly_988_, uint8_t v_skipConstInApp_989_, uint8_t v_skipInstances_990_, size_t v_sz_991_, size_t v_i_992_, lean_object* v_bs_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_usize_dec_lt(v_i_992_, v_sz_991_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec_ref(v_post_987_);
lean_dec_ref(v_pre_986_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_bs_993_);
return v___x_1001_;
}
else
{
lean_object* v_v_1002_; lean_object* v___x_1003_; 
v_v_1002_ = lean_array_uget_borrowed(v_bs_993_, v_i_992_);
lean_inc(v_v_1002_);
lean_inc_ref(v_post_987_);
lean_inc_ref(v_pre_986_);
v___x_1003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_986_, v_post_987_, v_usedLetOnly_988_, v_skipConstInApp_989_, v_skipInstances_990_, v_v_1002_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v_bs_x27_1006_; size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_unsigned_to_nat(0u);
v_bs_x27_1006_ = lean_array_uset(v_bs_993_, v_i_992_, v___x_1005_);
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_992_, v___x_1007_);
v___x_1009_ = lean_array_uset(v_bs_x27_1006_, v_i_992_, v_a_1004_);
v_i_992_ = v___x_1008_;
v_bs_993_ = v___x_1009_;
goto _start;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_bs_993_);
lean_dec_ref(v_post_987_);
lean_dec_ref(v_pre_986_);
v_a_1011_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1003_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1003_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1019_, lean_object* v_post_1020_, uint8_t v_usedLetOnly_1021_, uint8_t v_skipConstInApp_1022_, uint8_t v_skipInstances_1023_, lean_object* v___x_1024_, lean_object* v___y_1025_, lean_object* v_b_1026_, lean_object* v_a_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1019_, v_post_1020_, v_usedLetOnly_1021_, v_skipConstInApp_1022_, v_skipInstances_1023_, v___x_1024_, v___y_1025_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1043_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = lean_array_fset(v_b_1026_, v_a_1027_, v_a_1034_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v_b_1026_);
v_a_1044_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1033_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1033_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1052_, lean_object* v_post_1053_, lean_object* v_usedLetOnly_1054_, lean_object* v_skipConstInApp_1055_, lean_object* v_skipInstances_1056_, lean_object* v___x_1057_, lean_object* v___y_1058_, lean_object* v_b_1059_, lean_object* v_a_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_usedLetOnly_boxed_1066_; uint8_t v_skipConstInApp_boxed_1067_; uint8_t v_skipInstances_boxed_1068_; lean_object* v_res_1069_; 
v_usedLetOnly_boxed_1066_ = lean_unbox(v_usedLetOnly_1054_);
v_skipConstInApp_boxed_1067_ = lean_unbox(v_skipConstInApp_1055_);
v_skipInstances_boxed_1068_ = lean_unbox(v_skipInstances_1056_);
v_res_1069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1052_, v_post_1053_, v_usedLetOnly_boxed_1066_, v_skipConstInApp_boxed_1067_, v_skipInstances_boxed_1068_, v___x_1057_, v___y_1058_, v_b_1059_, v_a_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v_a_1060_);
lean_dec(v___y_1058_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1070_, lean_object* v___x_1071_, lean_object* v_pre_1072_, lean_object* v_post_1073_, uint8_t v_usedLetOnly_1074_, uint8_t v_skipConstInApp_1075_, uint8_t v_skipInstances_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___y_1086_; uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_lt(v_a_1077_, v_upperBound_1070_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1072_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_b_1078_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_array_fget_borrowed(v_b_1078_, v_a_1077_);
v___x_1112_ = lean_array_get_size(v___x_1071_);
v___x_1113_ = lean_nat_dec_lt(v_a_1077_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___f_1117_; 
lean_inc(v___x_1111_);
v___x_1114_ = lean_box(v_usedLetOnly_1074_);
v___x_1115_ = lean_box(v_skipConstInApp_1075_);
v___x_1116_ = lean_box(v_skipInstances_1076_);
lean_inc(v_a_1077_);
lean_inc(v___y_1079_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1072_);
v___f_1117_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1117_, 0, v_pre_1072_);
lean_closure_set(v___f_1117_, 1, v_post_1073_);
lean_closure_set(v___f_1117_, 2, v___x_1114_);
lean_closure_set(v___f_1117_, 3, v___x_1115_);
lean_closure_set(v___f_1117_, 4, v___x_1116_);
lean_closure_set(v___f_1117_, 5, v___x_1111_);
lean_closure_set(v___f_1117_, 6, v___y_1079_);
lean_closure_set(v___f_1117_, 7, v_b_1078_);
lean_closure_set(v___f_1117_, 8, v_a_1077_);
v___y_1086_ = v___f_1117_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1118_; uint8_t v_isInstance_1119_; 
v___x_1118_ = lean_array_fget_borrowed(v___x_1071_, v_a_1077_);
v_isInstance_1119_ = lean_ctor_get_uint8(v___x_1118_, sizeof(void*)*1 + 4);
if (v_isInstance_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___f_1123_; 
lean_inc(v___x_1111_);
v___x_1120_ = lean_box(v_usedLetOnly_1074_);
v___x_1121_ = lean_box(v_skipConstInApp_1075_);
v___x_1122_ = lean_box(v_skipInstances_1076_);
lean_inc(v_a_1077_);
lean_inc(v___y_1079_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1072_);
v___f_1123_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1123_, 0, v_pre_1072_);
lean_closure_set(v___f_1123_, 1, v_post_1073_);
lean_closure_set(v___f_1123_, 2, v___x_1120_);
lean_closure_set(v___f_1123_, 3, v___x_1121_);
lean_closure_set(v___f_1123_, 4, v___x_1122_);
lean_closure_set(v___f_1123_, 5, v___x_1111_);
lean_closure_set(v___f_1123_, 6, v___y_1079_);
lean_closure_set(v___f_1123_, 7, v_b_1078_);
lean_closure_set(v___f_1123_, 8, v_a_1077_);
v___y_1086_ = v___f_1123_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1124_; lean_object* v___f_1125_; 
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_b_1078_);
v___f_1125_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1125_, 0, v___x_1124_);
v___y_1086_ = v___f_1125_;
goto v___jp_1085_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1087_; 
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
v___x_1087_ = lean_apply_5(v___y_1086_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1100_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1100_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1100_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
if (lean_obj_tag(v_a_1088_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1072_);
v_a_1092_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_a_1088_, 1);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_a_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1090_);
v_a_1096_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v_a_1088_, 1);
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_add(v_a_1077_, v___x_1097_);
lean_dec(v_a_1077_);
v_a_1077_ = v___x_1098_;
v_b_1078_ = v_a_1096_;
goto _start;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1072_);
v_a_1101_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1087_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1087_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1126_, lean_object* v_pre_1127_, lean_object* v_post_1128_, uint8_t v_usedLetOnly_1129_, uint8_t v_skipConstInApp_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_f_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; 
if (lean_obj_tag(v_x_1131_) == 5)
{
lean_object* v_fn_1189_; lean_object* v_arg_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_fn_1189_ = lean_ctor_get(v_x_1131_, 0);
lean_inc_ref(v_fn_1189_);
v_arg_1190_ = lean_ctor_get(v_x_1131_, 1);
lean_inc_ref(v_arg_1190_);
lean_dec_ref_known(v_x_1131_, 2);
v___x_1191_ = lean_array_set(v_x_1132_, v_x_1133_, v_arg_1190_);
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_sub(v_x_1133_, v___x_1192_);
lean_dec(v_x_1133_);
v_x_1131_ = v_fn_1189_;
v_x_1132_ = v___x_1191_;
v_x_1133_ = v___x_1193_;
goto _start;
}
else
{
lean_dec(v_x_1133_);
if (v_skipConstInApp_1130_ == 0)
{
goto v___jp_1186_;
}
else
{
uint8_t v___x_1195_; 
v___x_1195_ = l_Lean_Expr_isConst(v_x_1131_);
if (v___x_1195_ == 0)
{
goto v___jp_1186_;
}
else
{
v_f_1141_ = v_x_1131_;
v___y_1142_ = v___y_1134_;
v___y_1143_ = v___y_1135_;
v___y_1144_ = v___y_1136_;
v___y_1145_ = v___y_1137_;
v___y_1146_ = v___y_1138_;
goto v___jp_1140_;
}
}
}
v___jp_1140_:
{
if (v_skipInstances_1126_ == 0)
{
size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v_sz_1147_ = lean_array_size(v_x_1132_);
v___x_1148_ = ((size_t)0ULL);
lean_inc_ref(v_post_1128_);
lean_inc_ref(v_pre_1127_);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1127_, v_post_1128_, v_usedLetOnly_1129_, v_skipConstInApp_1130_, v_skipInstances_1126_, v_sz_1147_, v___x_1148_, v_x_1132_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Lean_mkAppN(v_f_1141_, v_a_1150_);
lean_dec(v_a_1150_);
v___x_1152_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1127_, v_post_1128_, v_usedLetOnly_1129_, v_skipConstInApp_1130_, v_skipInstances_1126_, v___x_1151_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1152_;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_f_1141_);
lean_dec_ref(v_post_1128_);
lean_dec_ref(v_pre_1127_);
v_a_1153_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1149_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1149_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_array_get_size(v_x_1132_);
lean_inc_ref(v_f_1141_);
v___x_1162_ = l_Lean_Meta_getFunInfoNArgs(v_f_1141_, v___x_1161_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_paramInfo_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_paramInfo_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc_ref(v_paramInfo_1164_);
lean_dec(v_a_1163_);
v___x_1165_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1128_);
lean_inc_ref(v_pre_1127_);
v___x_1166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1161_, v_paramInfo_1164_, v_pre_1127_, v_post_1128_, v_usedLetOnly_1129_, v_skipConstInApp_1130_, v_skipInstances_1126_, v___x_1165_, v_x_1132_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec_ref(v_paramInfo_1164_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = l_Lean_mkAppN(v_f_1141_, v_a_1167_);
lean_dec(v_a_1167_);
v___x_1169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1127_, v_post_1128_, v_usedLetOnly_1129_, v_skipConstInApp_1130_, v_skipInstances_1126_, v___x_1168_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1169_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_f_1141_);
lean_dec_ref(v_post_1128_);
lean_dec_ref(v_pre_1127_);
v_a_1170_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1166_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_f_1141_);
lean_dec_ref(v_x_1132_);
lean_dec_ref(v_post_1128_);
lean_dec_ref(v_pre_1127_);
v_a_1178_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1162_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1162_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
v___jp_1186_:
{
lean_object* v___x_1187_; 
lean_inc_ref(v_post_1128_);
lean_inc_ref(v_pre_1127_);
v___x_1187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1127_, v_post_1128_, v_usedLetOnly_1129_, v_skipConstInApp_1130_, v_skipInstances_1126_, v_x_1131_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v_f_1141_ = v_a_1188_;
v___y_1142_ = v___y_1134_;
v___y_1143_ = v___y_1135_;
v___y_1144_ = v___y_1136_;
v___y_1145_ = v___y_1137_;
v___y_1146_ = v___y_1138_;
goto v___jp_1140_;
}
else
{
lean_dec_ref(v_x_1132_);
lean_dec_ref(v_post_1128_);
lean_dec_ref(v_pre_1127_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1196_, lean_object* v_pre_1197_, lean_object* v_e_1198_, lean_object* v_post_1199_, uint8_t v_usedLetOnly_1200_, uint8_t v_skipConstInApp_1201_, uint8_t v_skipInstances_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Core_checkSystem(v___x_1196_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref_known(v___x_1209_, 1);
lean_inc_ref(v_pre_1197_);
lean_inc(v___y_1207_);
lean_inc_ref(v___y_1206_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
lean_inc_ref(v_e_1198_);
v___x_1210_ = lean_apply_6(v_pre_1197_, v_e_1198_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, lean_box(0));
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1259_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1259_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1259_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___y_1216_; 
switch(lean_obj_tag(v_a_1211_))
{
case 0:
{
lean_object* v_e_1251_; lean_object* v___x_1253_; 
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_e_1198_);
lean_dec_ref(v_pre_1197_);
v_e_1251_ = lean_ctor_get(v_a_1211_, 0);
lean_inc_ref(v_e_1251_);
lean_dec_ref_known(v_a_1211_, 1);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_e_1251_);
v___x_1253_ = v___x_1213_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_e_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
case 1:
{
lean_object* v_e_1255_; lean_object* v___x_1256_; 
lean_del_object(v___x_1213_);
lean_dec_ref(v_e_1198_);
v_e_1255_ = lean_ctor_get(v_a_1211_, 0);
lean_inc_ref(v_e_1255_);
lean_dec_ref_known(v_a_1211_, 1);
v___x_1256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v_e_1255_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1256_;
}
default: 
{
lean_object* v_e_x3f_1257_; 
lean_del_object(v___x_1213_);
v_e_x3f_1257_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_e_x3f_1257_);
lean_dec_ref_known(v_a_1211_, 1);
if (lean_obj_tag(v_e_x3f_1257_) == 0)
{
v___y_1216_ = v_e_1198_;
goto v___jp_1215_;
}
else
{
lean_object* v_val_1258_; 
lean_dec_ref(v_e_1198_);
v_val_1258_ = lean_ctor_get(v_e_x3f_1257_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_e_x3f_1257_, 1);
v___y_1216_ = v_val_1258_;
goto v___jp_1215_;
}
}
}
v___jp_1215_:
{
switch(lean_obj_tag(v___y_1216_))
{
case 7:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___x_1217_, v___y_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1218_;
}
case 6:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___x_1219_, v___y_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1220_;
}
case 8:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___x_1221_, v___y_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1222_;
}
case 5:
{
lean_object* v_dummy_1223_; lean_object* v_nargs_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_dummy_1223_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1224_ = l_Lean_Expr_getAppNumArgs(v___y_1216_);
lean_inc(v_nargs_1224_);
v___x_1225_ = lean_mk_array(v_nargs_1224_, v_dummy_1223_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_sub(v_nargs_1224_, v___x_1226_);
lean_dec(v_nargs_1224_);
v___x_1228_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1202_, v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v___y_1216_, v___x_1225_, v___x_1227_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1228_;
}
case 10:
{
lean_object* v_data_1229_; lean_object* v_expr_1230_; lean_object* v___x_1231_; 
v_data_1229_ = lean_ctor_get(v___y_1216_, 0);
v_expr_1230_ = lean_ctor_get(v___y_1216_, 1);
lean_inc_ref(v_expr_1230_);
lean_inc_ref(v_post_1199_);
lean_inc_ref(v_pre_1197_);
v___x_1231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v_expr_1230_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; size_t v___x_1233_; size_t v___x_1234_; uint8_t v___x_1235_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1233_ = lean_ptr_addr(v_expr_1230_);
v___x_1234_ = lean_ptr_addr(v_a_1232_);
v___x_1235_ = lean_usize_dec_eq(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_inc(v_data_1229_);
lean_dec_ref_known(v___y_1216_, 2);
v___x_1236_ = l_Lean_Expr_mdata___override(v_data_1229_, v_a_1232_);
v___x_1237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___x_1236_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_a_1232_);
v___x_1238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___y_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1238_;
}
}
else
{
lean_dec_ref_known(v___y_1216_, 2);
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_pre_1197_);
return v___x_1231_;
}
}
case 11:
{
lean_object* v_typeName_1239_; lean_object* v_idx_1240_; lean_object* v_struct_1241_; lean_object* v___x_1242_; 
v_typeName_1239_ = lean_ctor_get(v___y_1216_, 0);
v_idx_1240_ = lean_ctor_get(v___y_1216_, 1);
v_struct_1241_ = lean_ctor_get(v___y_1216_, 2);
lean_inc_ref(v_struct_1241_);
lean_inc_ref(v_post_1199_);
lean_inc_ref(v_pre_1197_);
v___x_1242_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v_struct_1241_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; size_t v___x_1244_; size_t v___x_1245_; uint8_t v___x_1246_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = lean_ptr_addr(v_struct_1241_);
v___x_1245_ = lean_ptr_addr(v_a_1243_);
v___x_1246_ = lean_usize_dec_eq(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_inc(v_idx_1240_);
lean_inc(v_typeName_1239_);
lean_dec_ref_known(v___y_1216_, 3);
v___x_1247_ = l_Lean_Expr_proj___override(v_typeName_1239_, v_idx_1240_, v_a_1243_);
v___x_1248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___x_1247_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; 
lean_dec(v_a_1243_);
v___x_1249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___y_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1249_;
}
}
else
{
lean_dec_ref_known(v___y_1216_, 3);
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_pre_1197_);
return v___x_1242_;
}
}
default: 
{
lean_object* v___x_1250_; 
v___x_1250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1197_, v_post_1199_, v_usedLetOnly_1200_, v_skipConstInApp_1201_, v_skipInstances_1202_, v___y_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_e_1198_);
lean_dec_ref(v_pre_1197_);
v_a_1260_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1210_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1210_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_post_1199_);
lean_dec_ref(v_e_1198_);
lean_dec_ref(v_pre_1197_);
v_a_1268_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1209_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1209_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1276_, lean_object* v_pre_1277_, lean_object* v_e_1278_, lean_object* v_post_1279_, lean_object* v_usedLetOnly_1280_, lean_object* v_skipConstInApp_1281_, lean_object* v_skipInstances_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_usedLetOnly_boxed_1289_; uint8_t v_skipConstInApp_boxed_1290_; uint8_t v_skipInstances_boxed_1291_; lean_object* v_res_1292_; 
v_usedLetOnly_boxed_1289_ = lean_unbox(v_usedLetOnly_1280_);
v_skipConstInApp_boxed_1290_ = lean_unbox(v_skipConstInApp_1281_);
v_skipInstances_boxed_1291_ = lean_unbox(v_skipInstances_1282_);
v_res_1292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1276_, v_pre_1277_, v_e_1278_, v_post_1279_, v_usedLetOnly_boxed_1289_, v_skipConstInApp_boxed_1290_, v_skipInstances_boxed_1291_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1293_, lean_object* v_post_1294_, uint8_t v_usedLetOnly_1295_, uint8_t v_skipConstInApp_1296_, uint8_t v_skipInstances_1297_, lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_inc(v_a_1299_);
v___x_1305_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1305_, 0, lean_box(0));
lean_closure_set(v___x_1305_, 1, lean_box(0));
lean_closure_set(v___x_1305_, 2, v_a_1299_);
v___x_1306_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1305_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1341_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1341_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1341_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1307_, v_e_1298_);
lean_dec(v_a_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; 
lean_del_object(v___x_1309_);
v___x_1312_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1313_ = lean_box(v_usedLetOnly_1295_);
v___x_1314_ = lean_box(v_skipConstInApp_1296_);
v___x_1315_ = lean_box(v_skipInstances_1297_);
lean_inc_ref(v_e_1298_);
v___f_1316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1316_, 0, v___x_1312_);
lean_closure_set(v___f_1316_, 1, v_pre_1293_);
lean_closure_set(v___f_1316_, 2, v_e_1298_);
lean_closure_set(v___f_1316_, 3, v_post_1294_);
lean_closure_set(v___f_1316_, 4, v___x_1313_);
lean_closure_set(v___f_1316_, 5, v___x_1314_);
lean_closure_set(v___f_1316_, 6, v___x_1315_);
v___x_1317_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1316_, v_a_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___f_1319_; lean_object* v___x_1320_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_n(v_a_1318_, 2);
lean_dec_ref_known(v___x_1317_, 1);
lean_inc(v_a_1299_);
v___f_1319_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1319_, 0, v_a_1299_);
lean_closure_set(v___f_1319_, 1, v_e_1298_);
lean_closure_set(v___f_1319_, 2, v_a_1318_);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1319_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v___x_1320_, 0);
lean_dec(v_unused_1328_);
v___x_1322_ = v___x_1320_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_dec(v___x_1320_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_a_1318_);
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1318_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1318_);
v_a_1329_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1320_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1320_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_dec_ref(v_e_1298_);
return v___x_1317_;
}
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1339_; 
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_post_1294_);
lean_dec_ref(v_pre_1293_);
v_val_1337_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1311_, 1);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v_val_1337_);
v___x_1339_ = v___x_1309_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_post_1294_);
lean_dec_ref(v_pre_1293_);
v_a_1342_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1306_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1306_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1350_, lean_object* v_pre_1351_, lean_object* v_post_1352_, lean_object* v_usedLetOnly_1353_, lean_object* v_skipConstInApp_1354_, lean_object* v_skipInstances_1355_, lean_object* v_body_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v_usedLetOnly_boxed_1364_; uint8_t v_skipConstInApp_boxed_1365_; uint8_t v_skipInstances_boxed_1366_; lean_object* v_res_1367_; 
v_usedLetOnly_boxed_1364_ = lean_unbox(v_usedLetOnly_1353_);
v_skipConstInApp_boxed_1365_ = lean_unbox(v_skipConstInApp_1354_);
v_skipInstances_boxed_1366_ = lean_unbox(v_skipInstances_1355_);
v_res_1367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1350_, v_pre_1351_, v_post_1352_, v_usedLetOnly_boxed_1364_, v_skipConstInApp_boxed_1365_, v_skipInstances_boxed_1366_, v_body_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1368_, lean_object* v_post_1369_, uint8_t v_usedLetOnly_1370_, uint8_t v_skipConstInApp_1371_, uint8_t v_skipInstances_1372_, lean_object* v_fvars_1373_, lean_object* v_e_1374_, lean_object* v_a_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
if (lean_obj_tag(v_e_1374_) == 7)
{
lean_object* v_binderName_1381_; lean_object* v_binderType_1382_; lean_object* v_body_1383_; uint8_t v_binderInfo_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_binderName_1381_ = lean_ctor_get(v_e_1374_, 0);
lean_inc(v_binderName_1381_);
v_binderType_1382_ = lean_ctor_get(v_e_1374_, 1);
lean_inc_ref(v_binderType_1382_);
v_body_1383_ = lean_ctor_get(v_e_1374_, 2);
lean_inc_ref(v_body_1383_);
v_binderInfo_1384_ = lean_ctor_get_uint8(v_e_1374_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1374_, 3);
v___x_1385_ = lean_expr_instantiate_rev(v_binderType_1382_, v_fvars_1373_);
lean_dec_ref(v_binderType_1382_);
lean_inc_ref(v_post_1369_);
lean_inc_ref(v_pre_1368_);
v___x_1386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1368_, v_post_1369_, v_usedLetOnly_1370_, v_skipConstInApp_1371_, v_skipInstances_1372_, v___x_1385_, v_a_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = lean_box(v_usedLetOnly_1370_);
v___x_1389_ = lean_box(v_skipConstInApp_1371_);
v___x_1390_ = lean_box(v_skipInstances_1372_);
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1391_, 0, v_fvars_1373_);
lean_closure_set(v___f_1391_, 1, v_pre_1368_);
lean_closure_set(v___f_1391_, 2, v_post_1369_);
lean_closure_set(v___f_1391_, 3, v___x_1388_);
lean_closure_set(v___f_1391_, 4, v___x_1389_);
lean_closure_set(v___f_1391_, 5, v___x_1390_);
lean_closure_set(v___f_1391_, 6, v_body_1383_);
v___x_1392_ = 0;
v___x_1393_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1381_, v_binderInfo_1384_, v_a_1387_, v___f_1391_, v___x_1392_, v_a_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1393_;
}
else
{
lean_dec_ref(v_body_1383_);
lean_dec(v_binderName_1381_);
lean_dec_ref(v_fvars_1373_);
lean_dec_ref(v_post_1369_);
lean_dec_ref(v_pre_1368_);
return v___x_1386_;
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_expr_instantiate_rev(v_e_1374_, v_fvars_1373_);
lean_dec_ref(v_e_1374_);
lean_inc_ref(v_post_1369_);
lean_inc_ref(v_pre_1368_);
v___x_1395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1368_, v_post_1369_, v_usedLetOnly_1370_, v_skipConstInApp_1371_, v_skipInstances_1372_, v___x_1394_, v_a_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; uint8_t v___x_1397_; uint8_t v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = 0;
v___x_1398_ = 1;
v___x_1399_ = 1;
v___x_1400_ = l_Lean_Meta_mkForallFVars(v_fvars_1373_, v_a_1396_, v___x_1397_, v_usedLetOnly_1370_, v___x_1398_, v___x_1399_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec_ref(v_fvars_1373_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1368_, v_post_1369_, v_usedLetOnly_1370_, v_skipConstInApp_1371_, v_skipInstances_1372_, v_a_1401_, v_a_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1402_;
}
else
{
lean_dec_ref(v_post_1369_);
lean_dec_ref(v_pre_1368_);
return v___x_1400_;
}
}
else
{
lean_dec_ref(v_fvars_1373_);
lean_dec_ref(v_post_1369_);
lean_dec_ref(v_pre_1368_);
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1403_, lean_object* v_pre_1404_, lean_object* v_post_1405_, uint8_t v_usedLetOnly_1406_, uint8_t v_skipConstInApp_1407_, uint8_t v_skipInstances_1408_, lean_object* v_body_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_array_push(v_fvars_1403_, v_x_1410_);
v___x_1418_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1404_, v_post_1405_, v_usedLetOnly_1406_, v_skipConstInApp_1407_, v_skipInstances_1408_, v___x_1417_, v_body_1409_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1419_, lean_object* v_post_1420_, lean_object* v_usedLetOnly_1421_, lean_object* v_skipConstInApp_1422_, lean_object* v_skipInstances_1423_, lean_object* v_e_1424_, lean_object* v_a_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v_usedLetOnly_boxed_1431_; uint8_t v_skipConstInApp_boxed_1432_; uint8_t v_skipInstances_boxed_1433_; lean_object* v_res_1434_; 
v_usedLetOnly_boxed_1431_ = lean_unbox(v_usedLetOnly_1421_);
v_skipConstInApp_boxed_1432_ = lean_unbox(v_skipConstInApp_1422_);
v_skipInstances_boxed_1433_ = lean_unbox(v_skipInstances_1423_);
v_res_1434_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1419_, v_post_1420_, v_usedLetOnly_boxed_1431_, v_skipConstInApp_boxed_1432_, v_skipInstances_boxed_1433_, v_e_1424_, v_a_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v_a_1425_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1435_, lean_object* v_post_1436_, lean_object* v_usedLetOnly_1437_, lean_object* v_skipConstInApp_1438_, lean_object* v_skipInstances_1439_, lean_object* v_sz_1440_, lean_object* v_i_1441_, lean_object* v_bs_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_usedLetOnly_boxed_1449_; uint8_t v_skipConstInApp_boxed_1450_; uint8_t v_skipInstances_boxed_1451_; size_t v_sz_boxed_1452_; size_t v_i_boxed_1453_; lean_object* v_res_1454_; 
v_usedLetOnly_boxed_1449_ = lean_unbox(v_usedLetOnly_1437_);
v_skipConstInApp_boxed_1450_ = lean_unbox(v_skipConstInApp_1438_);
v_skipInstances_boxed_1451_ = lean_unbox(v_skipInstances_1439_);
v_sz_boxed_1452_ = lean_unbox_usize(v_sz_1440_);
lean_dec(v_sz_1440_);
v_i_boxed_1453_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_res_1454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1435_, v_post_1436_, v_usedLetOnly_boxed_1449_, v_skipConstInApp_boxed_1450_, v_skipInstances_boxed_1451_, v_sz_boxed_1452_, v_i_boxed_1453_, v_bs_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1455_, lean_object* v_post_1456_, lean_object* v_usedLetOnly_1457_, lean_object* v_skipConstInApp_1458_, lean_object* v_skipInstances_1459_, lean_object* v_e_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_usedLetOnly_boxed_1467_; uint8_t v_skipConstInApp_boxed_1468_; uint8_t v_skipInstances_boxed_1469_; lean_object* v_res_1470_; 
v_usedLetOnly_boxed_1467_ = lean_unbox(v_usedLetOnly_1457_);
v_skipConstInApp_boxed_1468_ = lean_unbox(v_skipConstInApp_1458_);
v_skipInstances_boxed_1469_ = lean_unbox(v_skipInstances_1459_);
v_res_1470_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1455_, v_post_1456_, v_usedLetOnly_boxed_1467_, v_skipConstInApp_boxed_1468_, v_skipInstances_boxed_1469_, v_e_1460_, v_a_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_a_1461_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1471_, lean_object* v_post_1472_, lean_object* v_usedLetOnly_1473_, lean_object* v_skipConstInApp_1474_, lean_object* v_skipInstances_1475_, lean_object* v_fvars_1476_, lean_object* v_e_1477_, lean_object* v_a_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v_usedLetOnly_boxed_1484_; uint8_t v_skipConstInApp_boxed_1485_; uint8_t v_skipInstances_boxed_1486_; lean_object* v_res_1487_; 
v_usedLetOnly_boxed_1484_ = lean_unbox(v_usedLetOnly_1473_);
v_skipConstInApp_boxed_1485_ = lean_unbox(v_skipConstInApp_1474_);
v_skipInstances_boxed_1486_ = lean_unbox(v_skipInstances_1475_);
v_res_1487_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1471_, v_post_1472_, v_usedLetOnly_boxed_1484_, v_skipConstInApp_boxed_1485_, v_skipInstances_boxed_1486_, v_fvars_1476_, v_e_1477_, v_a_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v_a_1478_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1488_, lean_object* v_post_1489_, lean_object* v_usedLetOnly_1490_, lean_object* v_skipConstInApp_1491_, lean_object* v_skipInstances_1492_, lean_object* v_fvars_1493_, lean_object* v_e_1494_, lean_object* v_a_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_usedLetOnly_boxed_1501_; uint8_t v_skipConstInApp_boxed_1502_; uint8_t v_skipInstances_boxed_1503_; lean_object* v_res_1504_; 
v_usedLetOnly_boxed_1501_ = lean_unbox(v_usedLetOnly_1490_);
v_skipConstInApp_boxed_1502_ = lean_unbox(v_skipConstInApp_1491_);
v_skipInstances_boxed_1503_ = lean_unbox(v_skipInstances_1492_);
v_res_1504_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1488_, v_post_1489_, v_usedLetOnly_boxed_1501_, v_skipConstInApp_boxed_1502_, v_skipInstances_boxed_1503_, v_fvars_1493_, v_e_1494_, v_a_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v_a_1495_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1505_, lean_object* v_post_1506_, lean_object* v_usedLetOnly_1507_, lean_object* v_skipConstInApp_1508_, lean_object* v_skipInstances_1509_, lean_object* v_fvars_1510_, lean_object* v_e_1511_, lean_object* v_a_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v_usedLetOnly_boxed_1518_; uint8_t v_skipConstInApp_boxed_1519_; uint8_t v_skipInstances_boxed_1520_; lean_object* v_res_1521_; 
v_usedLetOnly_boxed_1518_ = lean_unbox(v_usedLetOnly_1507_);
v_skipConstInApp_boxed_1519_ = lean_unbox(v_skipConstInApp_1508_);
v_skipInstances_boxed_1520_ = lean_unbox(v_skipInstances_1509_);
v_res_1521_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1505_, v_post_1506_, v_usedLetOnly_boxed_1518_, v_skipConstInApp_boxed_1519_, v_skipInstances_boxed_1520_, v_fvars_1510_, v_e_1511_, v_a_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v_a_1512_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1522_, lean_object* v___x_1523_, lean_object* v_pre_1524_, lean_object* v_post_1525_, lean_object* v_usedLetOnly_1526_, lean_object* v_skipConstInApp_1527_, lean_object* v_skipInstances_1528_, lean_object* v_a_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v_usedLetOnly_boxed_1537_; uint8_t v_skipConstInApp_boxed_1538_; uint8_t v_skipInstances_boxed_1539_; lean_object* v_res_1540_; 
v_usedLetOnly_boxed_1537_ = lean_unbox(v_usedLetOnly_1526_);
v_skipConstInApp_boxed_1538_ = lean_unbox(v_skipConstInApp_1527_);
v_skipInstances_boxed_1539_ = lean_unbox(v_skipInstances_1528_);
v_res_1540_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1522_, v___x_1523_, v_pre_1524_, v_post_1525_, v_usedLetOnly_boxed_1537_, v_skipConstInApp_boxed_1538_, v_skipInstances_boxed_1539_, v_a_1529_, v_b_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___x_1523_);
lean_dec(v_upperBound_1522_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1541_, lean_object* v_pre_1542_, lean_object* v_post_1543_, lean_object* v_usedLetOnly_1544_, lean_object* v_skipConstInApp_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_skipInstances_boxed_1555_; uint8_t v_usedLetOnly_boxed_1556_; uint8_t v_skipConstInApp_boxed_1557_; lean_object* v_res_1558_; 
v_skipInstances_boxed_1555_ = lean_unbox(v_skipInstances_1541_);
v_usedLetOnly_boxed_1556_ = lean_unbox(v_usedLetOnly_1544_);
v_skipConstInApp_boxed_1557_ = lean_unbox(v_skipConstInApp_1545_);
v_res_1558_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1555_, v_pre_1542_, v_post_1543_, v_usedLetOnly_boxed_1556_, v_skipConstInApp_boxed_1557_, v_x_1546_, v_x_1547_, v_x_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
return v_res_1558_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_unsigned_to_nat(16u);
v___x_1561_ = lean_mk_array(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1566_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1566_, 0, lean_box(0));
lean_closure_set(v___x_1566_, 1, lean_box(0));
lean_closure_set(v___x_1566_, 2, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1567_, lean_object* v_pre_1568_, lean_object* v_post_1569_, uint8_t v_usedLetOnly_1570_, uint8_t v_skipConstInApp_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_a_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1577_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1578_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1577_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = 0;
v___x_1581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1568_, v_post_1569_, v_usedLetOnly_1570_, v_skipConstInApp_1571_, v___x_1580_, v_input_1567_, v_a_1579_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1583_, 0, lean_box(0));
lean_closure_set(v___x_1583_, 1, lean_box(0));
lean_closure_set(v___x_1583_, 2, v_a_1579_);
v___x_1584_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1583_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1592_);
v___x_1586_ = v___x_1584_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v___x_1584_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_a_1582_);
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1582_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
else
{
lean_dec(v_a_1579_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1593_, lean_object* v_pre_1594_, lean_object* v_post_1595_, lean_object* v_usedLetOnly_1596_, lean_object* v_skipConstInApp_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v_usedLetOnly_boxed_1603_; uint8_t v_skipConstInApp_boxed_1604_; lean_object* v_res_1605_; 
v_usedLetOnly_boxed_1603_ = lean_unbox(v_usedLetOnly_1596_);
v_skipConstInApp_boxed_1604_ = lean_unbox(v_skipConstInApp_1597_);
v_res_1605_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1593_, v_pre_1594_, v_post_1595_, v_usedLetOnly_boxed_1603_, v_skipConstInApp_boxed_1604_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1627_; 
v___x_1614_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1608_, v_a_1612_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1627_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1627_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_unbox(v_a_1615_);
lean_dec(v_a_1615_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1621_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_e_1608_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_e_1608_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v___f_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1617_);
v___f_1623_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1624_ = 0;
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1626_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1608_, v___x_1625_, v___f_1623_, v___x_1624_, v___x_1624_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1635_, lean_object* v___x_1636_, lean_object* v_pre_1637_, lean_object* v_post_1638_, uint8_t v_usedLetOnly_1639_, uint8_t v_skipConstInApp_1640_, uint8_t v_skipInstances_1641_, lean_object* v___x_1642_, lean_object* v_inst_1643_, lean_object* v_R_1644_, lean_object* v_a_1645_, lean_object* v_b_1646_, lean_object* v_c_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1635_, v___x_1636_, v_pre_1637_, v_post_1638_, v_usedLetOnly_1639_, v_skipConstInApp_1640_, v_skipInstances_1641_, v_a_1645_, v_b_1646_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1655_ = _args[0];
lean_object* v___x_1656_ = _args[1];
lean_object* v_pre_1657_ = _args[2];
lean_object* v_post_1658_ = _args[3];
lean_object* v_usedLetOnly_1659_ = _args[4];
lean_object* v_skipConstInApp_1660_ = _args[5];
lean_object* v_skipInstances_1661_ = _args[6];
lean_object* v___x_1662_ = _args[7];
lean_object* v_inst_1663_ = _args[8];
lean_object* v_R_1664_ = _args[9];
lean_object* v_a_1665_ = _args[10];
lean_object* v_b_1666_ = _args[11];
lean_object* v_c_1667_ = _args[12];
lean_object* v___y_1668_ = _args[13];
lean_object* v___y_1669_ = _args[14];
lean_object* v___y_1670_ = _args[15];
lean_object* v___y_1671_ = _args[16];
lean_object* v___y_1672_ = _args[17];
lean_object* v___y_1673_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1674_; uint8_t v_skipConstInApp_boxed_1675_; uint8_t v_skipInstances_boxed_1676_; lean_object* v_res_1677_; 
v_usedLetOnly_boxed_1674_ = lean_unbox(v_usedLetOnly_1659_);
v_skipConstInApp_boxed_1675_ = lean_unbox(v_skipConstInApp_1660_);
v_skipInstances_boxed_1676_ = lean_unbox(v_skipInstances_1661_);
v_res_1677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1655_, v___x_1656_, v_pre_1657_, v_post_1658_, v_usedLetOnly_boxed_1674_, v_skipConstInApp_boxed_1675_, v_skipInstances_boxed_1676_, v___x_1662_, v_inst_1663_, v_R_1664_, v_a_1665_, v_b_1666_, v_c_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___x_1662_);
lean_dec_ref(v___x_1656_);
lean_dec(v_upperBound_1655_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1678_, lean_object* v_m_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1679_, v_a_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1682_, lean_object* v_m_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1682_, v_m_1683_, v_a_1684_);
lean_dec_ref(v_a_1684_);
lean_dec_ref(v_m_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1686_, lean_object* v_name_1687_, uint8_t v_bi_1688_, lean_object* v_type_1689_, lean_object* v_k_1690_, uint8_t v_kind_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1687_, v_bi_1688_, v_type_1689_, v_k_1690_, v_kind_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_name_1700_, lean_object* v_bi_1701_, lean_object* v_type_1702_, lean_object* v_k_1703_, lean_object* v_kind_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v_bi_boxed_1711_; uint8_t v_kind_boxed_1712_; lean_object* v_res_1713_; 
v_bi_boxed_1711_ = lean_unbox(v_bi_1701_);
v_kind_boxed_1712_ = lean_unbox(v_kind_1704_);
v_res_1713_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1699_, v_name_1700_, v_bi_boxed_1711_, v_type_1702_, v_k_1703_, v_kind_boxed_1712_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1714_, lean_object* v_name_1715_, lean_object* v_type_1716_, lean_object* v_val_1717_, lean_object* v_k_1718_, uint8_t v_nondep_1719_, uint8_t v_kind_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1715_, v_type_1716_, v_val_1717_, v_k_1718_, v_nondep_1719_, v_kind_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_name_1729_, lean_object* v_type_1730_, lean_object* v_val_1731_, lean_object* v_k_1732_, lean_object* v_nondep_1733_, lean_object* v_kind_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v_nondep_boxed_1741_; uint8_t v_kind_boxed_1742_; lean_object* v_res_1743_; 
v_nondep_boxed_1741_ = lean_unbox(v_nondep_1733_);
v_kind_boxed_1742_ = lean_unbox(v_kind_1734_);
v_res_1743_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1728_, v_name_1729_, v_type_1730_, v_val_1731_, v_k_1732_, v_nondep_boxed_1741_, v_kind_boxed_1742_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1744_, lean_object* v_ref_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1745_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_ref_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1752_, v_ref_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1769_, lean_object* v_x_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1769_, v_x_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1778_, lean_object* v_m_1779_, lean_object* v_a_1780_, lean_object* v_b_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1779_, v_a_1780_, v_b_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1783_, lean_object* v_a_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1784_, v_x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1787_, lean_object* v_a_1788_, lean_object* v_x_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1787_, v_a_1788_, v_x_1789_);
lean_dec(v_x_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1791_, lean_object* v_a_1792_, lean_object* v_x_1793_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1792_, v_x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1795_, lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
uint8_t v_res_1798_; lean_object* v_r_1799_; 
v_res_1798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1795_, v_a_1796_, v_x_1797_);
lean_dec(v_x_1797_);
lean_dec_ref(v_a_1796_);
v_r_1799_ = lean_box(v_res_1798_);
return v_r_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1800_, lean_object* v_data_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1803_, lean_object* v_a_1804_, lean_object* v_b_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1804_, v_b_1805_, v_x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1808_, lean_object* v_i_1809_, lean_object* v_source_1810_, lean_object* v_target_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1809_, v_source_1810_, v_target_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1814_, v_x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v_env_1824_; lean_object* v___x_1825_; lean_object* v_mctx_1826_; lean_object* v_lctx_1827_; lean_object* v_options_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1823_ = lean_st_ref_get(v___y_1821_);
v_env_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_ref(v_env_1824_);
lean_dec(v___x_1823_);
v___x_1825_ = lean_st_ref_get(v___y_1819_);
v_mctx_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_mctx_1826_);
lean_dec(v___x_1825_);
v_lctx_1827_ = lean_ctor_get(v___y_1818_, 2);
v_options_1828_ = lean_ctor_get(v___y_1820_, 2);
lean_inc_ref(v_options_1828_);
lean_inc_ref(v_lctx_1827_);
v___x_1829_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1829_, 0, v_env_1824_);
lean_ctor_set(v___x_1829_, 1, v_mctx_1826_);
lean_ctor_set(v___x_1829_, 2, v_lctx_1827_);
lean_ctor_set(v___x_1829_, 3, v_options_1828_);
v___x_1830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_msgData_1817_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1839_; double v___x_1840_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_float_of_nat(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1844_, lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1897_; 
v_ref_1851_ = lean_ctor_get(v___y_1848_, 5);
v___x_1852_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1897_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1897_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v_traceState_1858_; lean_object* v_env_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_cache_1863_; lean_object* v_messages_1864_; lean_object* v_infoState_1865_; lean_object* v_snapshotTasks_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1896_; 
v___x_1857_ = lean_st_ref_take(v___y_1849_);
v_traceState_1858_ = lean_ctor_get(v___x_1857_, 4);
v_env_1859_ = lean_ctor_get(v___x_1857_, 0);
v_nextMacroScope_1860_ = lean_ctor_get(v___x_1857_, 1);
v_ngen_1861_ = lean_ctor_get(v___x_1857_, 2);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1857_, 3);
v_cache_1863_ = lean_ctor_get(v___x_1857_, 5);
v_messages_1864_ = lean_ctor_get(v___x_1857_, 6);
v_infoState_1865_ = lean_ctor_get(v___x_1857_, 7);
v_snapshotTasks_1866_ = lean_ctor_get(v___x_1857_, 8);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1868_ = v___x_1857_;
v_isShared_1869_ = v_isSharedCheck_1896_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snapshotTasks_1866_);
lean_inc(v_infoState_1865_);
lean_inc(v_messages_1864_);
lean_inc(v_cache_1863_);
lean_inc(v_traceState_1858_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_ngen_1861_);
lean_inc(v_nextMacroScope_1860_);
lean_inc(v_env_1859_);
lean_dec(v___x_1857_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1896_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint64_t v_tid_1870_; lean_object* v_traces_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1895_; 
v_tid_1870_ = lean_ctor_get_uint64(v_traceState_1858_, sizeof(void*)*1);
v_traces_1871_ = lean_ctor_get(v_traceState_1858_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_traceState_1858_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1873_ = v_traceState_1858_;
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_traces_1871_);
lean_dec(v_traceState_1858_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; double v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1877_ = 0;
v___x_1878_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1879_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1879_, 0, v_cls_1844_);
lean_ctor_set(v___x_1879_, 1, v___x_1875_);
lean_ctor_set(v___x_1879_, 2, v___x_1878_);
lean_ctor_set_float(v___x_1879_, sizeof(void*)*3, v___x_1876_);
lean_ctor_set_float(v___x_1879_, sizeof(void*)*3 + 8, v___x_1876_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*3 + 16, v___x_1877_);
v___x_1880_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1881_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v_a_1853_);
lean_ctor_set(v___x_1881_, 2, v___x_1880_);
lean_inc(v_ref_1851_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_ref_1851_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_PersistentArray_push___redArg(v_traces_1871_, v___x_1882_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1883_);
v___x_1885_ = v___x_1873_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1883_);
lean_ctor_set_uint64(v_reuseFailAlloc_1894_, sizeof(void*)*1, v_tid_1870_);
v___x_1885_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 4, v___x_1885_);
v___x_1887_ = v___x_1868_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1859_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1863_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_messages_1864_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v_infoState_1865_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_snapshotTasks_1866_);
v___x_1887_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_st_ref_set(v___y_1849_, v___x_1887_);
v___x_1889_ = lean_box(0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1889_);
v___x_1891_ = v___x_1855_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1898_, v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1910_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__1));
v___x_1911_ = l_Lean_Name_append(v___x_1910_, v___x_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__3));
v___x_1914_ = l_Lean_stringToMessageData(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__5));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7(void){
_start:
{
uint8_t v___x_1918_; uint64_t v___x_1919_; 
v___x_1918_ = 1;
v___x_1919_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__8));
v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__10));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_e_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
if (lean_obj_tag(v_e_1926_) == 11)
{
lean_object* v_typeName_1938_; lean_object* v_idx_1939_; lean_object* v_struct_1940_; lean_object* v___x_1941_; lean_object* v_env_1942_; lean_object* v___x_1943_; 
v_typeName_1938_ = lean_ctor_get(v_e_1926_, 0);
v_idx_1939_ = lean_ctor_get(v_e_1926_, 1);
v_struct_1940_ = lean_ctor_get(v_e_1926_, 2);
v___x_1941_ = lean_st_ref_get(v___y_1930_);
v_env_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_ref(v_env_1942_);
lean_dec(v___x_1941_);
lean_inc(v_typeName_1938_);
v___x_1943_ = l_Lean_getStructureInfo_x3f(v_env_1942_, v_typeName_1938_);
if (lean_obj_tag(v___x_1943_) == 1)
{
lean_object* v_val_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2043_; 
v_val_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_2043_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_val_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2043_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_fieldNames_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v_fieldNames_1948_ = lean_ctor_get(v_val_1944_, 1);
lean_inc_ref(v_fieldNames_1948_);
lean_dec(v_val_1944_);
v___x_1949_ = lean_array_get_size(v_fieldNames_1948_);
v___x_1950_ = lean_nat_dec_lt(v_idx_1939_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v_options_1951_; uint8_t v_hasTrace_1952_; 
lean_dec_ref(v_fieldNames_1948_);
v_options_1951_ = lean_ctor_get(v___y_1929_, 2);
v_hasTrace_1952_ = lean_ctor_get_uint8(v_options_1951_, sizeof(void*)*1);
if (v_hasTrace_1952_ == 0)
{
lean_del_object(v___x_1946_);
goto v___jp_1932_;
}
else
{
lean_object* v_inheritedTraceOptions_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_inheritedTraceOptions_1953_ = lean_ctor_get(v___y_1929_, 13);
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1955_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_1956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1953_, v_options_1951_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_del_object(v___x_1946_);
goto v___jp_1932_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1957_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4);
lean_inc(v_idx_1939_);
v___x_1958_ = l_Nat_reprFast(v_idx_1939_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 3);
lean_ctor_set(v___x_1946_, 0, v___x_1958_);
v___x_1960_ = v___x_1946_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1961_ = l_Lean_MessageData_ofFormat(v___x_1960_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1957_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
lean_inc_ref(v_e_1926_);
v___x_1965_ = l_Lean_indentExpr(v_e_1926_);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1954_, v___x_1966_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_dec_ref_known(v___x_1967_, 1);
goto v___jp_1932_;
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref_known(v_e_1926_, 3);
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1977_; uint8_t v_foApprox_1978_; uint8_t v_ctxApprox_1979_; uint8_t v_quasiPatternApprox_1980_; uint8_t v_constApprox_1981_; uint8_t v_isDefEqStuckEx_1982_; uint8_t v_unificationHints_1983_; uint8_t v_proofIrrelevance_1984_; uint8_t v_assignSyntheticOpaque_1985_; uint8_t v_offsetCnstrs_1986_; uint8_t v_etaStruct_1987_; uint8_t v_univApprox_1988_; uint8_t v_iota_1989_; uint8_t v_beta_1990_; uint8_t v_proj_1991_; uint8_t v_zeta_1992_; uint8_t v_zetaDelta_1993_; uint8_t v_zetaUnused_1994_; uint8_t v_zetaHave_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2042_; 
lean_inc_ref(v_struct_1940_);
lean_inc(v_idx_1939_);
lean_dec_ref_known(v_e_1926_, 3);
v___x_1977_ = l_Lean_Meta_Context_config(v___y_1927_);
v_foApprox_1978_ = lean_ctor_get_uint8(v___x_1977_, 0);
v_ctxApprox_1979_ = lean_ctor_get_uint8(v___x_1977_, 1);
v_quasiPatternApprox_1980_ = lean_ctor_get_uint8(v___x_1977_, 2);
v_constApprox_1981_ = lean_ctor_get_uint8(v___x_1977_, 3);
v_isDefEqStuckEx_1982_ = lean_ctor_get_uint8(v___x_1977_, 4);
v_unificationHints_1983_ = lean_ctor_get_uint8(v___x_1977_, 5);
v_proofIrrelevance_1984_ = lean_ctor_get_uint8(v___x_1977_, 6);
v_assignSyntheticOpaque_1985_ = lean_ctor_get_uint8(v___x_1977_, 7);
v_offsetCnstrs_1986_ = lean_ctor_get_uint8(v___x_1977_, 8);
v_etaStruct_1987_ = lean_ctor_get_uint8(v___x_1977_, 10);
v_univApprox_1988_ = lean_ctor_get_uint8(v___x_1977_, 11);
v_iota_1989_ = lean_ctor_get_uint8(v___x_1977_, 12);
v_beta_1990_ = lean_ctor_get_uint8(v___x_1977_, 13);
v_proj_1991_ = lean_ctor_get_uint8(v___x_1977_, 14);
v_zeta_1992_ = lean_ctor_get_uint8(v___x_1977_, 15);
v_zetaDelta_1993_ = lean_ctor_get_uint8(v___x_1977_, 16);
v_zetaUnused_1994_ = lean_ctor_get_uint8(v___x_1977_, 17);
v_zetaHave_1995_ = lean_ctor_get_uint8(v___x_1977_, 18);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_1997_ = v___x_1977_;
v_isShared_1998_ = v_isSharedCheck_2042_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v___x_1977_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2042_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v_trackZetaDelta_1999_; lean_object* v_zetaDeltaSet_2000_; lean_object* v_lctx_2001_; lean_object* v_localInstances_2002_; lean_object* v_defEqCtx_x3f_2003_; lean_object* v_synthPendingDepth_2004_; lean_object* v_canUnfold_x3f_2005_; uint8_t v_univApprox_2006_; uint8_t v_inTypeClassResolution_2007_; uint8_t v_cacheInferType_2008_; uint8_t v___x_2009_; lean_object* v_config_2011_; 
v_trackZetaDelta_1999_ = lean_ctor_get_uint8(v___y_1927_, sizeof(void*)*7);
v_zetaDeltaSet_2000_ = lean_ctor_get(v___y_1927_, 1);
v_lctx_2001_ = lean_ctor_get(v___y_1927_, 2);
v_localInstances_2002_ = lean_ctor_get(v___y_1927_, 3);
v_defEqCtx_x3f_2003_ = lean_ctor_get(v___y_1927_, 4);
v_synthPendingDepth_2004_ = lean_ctor_get(v___y_1927_, 5);
v_canUnfold_x3f_2005_ = lean_ctor_get(v___y_1927_, 6);
v_univApprox_2006_ = lean_ctor_get_uint8(v___y_1927_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2007_ = lean_ctor_get_uint8(v___y_1927_, sizeof(void*)*7 + 2);
v_cacheInferType_2008_ = lean_ctor_get_uint8(v___y_1927_, sizeof(void*)*7 + 3);
v___x_2009_ = 1;
if (v_isShared_1998_ == 0)
{
v_config_2011_ = v___x_1997_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 0, v_foApprox_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 1, v_ctxApprox_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 2, v_quasiPatternApprox_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 3, v_constApprox_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 4, v_isDefEqStuckEx_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 5, v_unificationHints_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 6, v_proofIrrelevance_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 7, v_assignSyntheticOpaque_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 8, v_offsetCnstrs_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 10, v_etaStruct_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 11, v_univApprox_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 12, v_iota_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 13, v_beta_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 14, v_proj_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 15, v_zeta_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 16, v_zetaDelta_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 17, v_zetaUnused_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, 18, v_zetaHave_1995_);
v_config_2011_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
uint64_t v___x_2012_; uint64_t v___x_2013_; uint64_t v___x_2014_; lean_object* v___x_2015_; uint64_t v___x_2016_; uint64_t v___x_2017_; uint64_t v_key_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_ctor_set_uint8(v_config_2011_, 9, v___x_2009_);
v___x_2012_ = l_Lean_Meta_Context_configKey(v___y_1927_);
v___x_2013_ = 3ULL;
v___x_2014_ = lean_uint64_shift_right(v___x_2012_, v___x_2013_);
v___x_2015_ = lean_array_fget(v_fieldNames_1948_, v_idx_1939_);
lean_dec(v_idx_1939_);
lean_dec_ref(v_fieldNames_1948_);
v___x_2016_ = lean_uint64_shift_left(v___x_2014_, v___x_2013_);
v___x_2017_ = lean_uint64_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__7, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7);
v_key_2018_ = lean_uint64_lor(v___x_2016_, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2019_, 0, v_config_2011_);
lean_ctor_set_uint64(v___x_2019_, sizeof(void*)*1, v_key_2018_);
lean_inc(v_canUnfold_x3f_2005_);
lean_inc(v_synthPendingDepth_2004_);
lean_inc(v_defEqCtx_x3f_2003_);
lean_inc_ref(v_localInstances_2002_);
lean_inc_ref(v_lctx_2001_);
lean_inc(v_zetaDeltaSet_2000_);
v___x_2020_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_zetaDeltaSet_2000_);
lean_ctor_set(v___x_2020_, 2, v_lctx_2001_);
lean_ctor_set(v___x_2020_, 3, v_localInstances_2002_);
lean_ctor_set(v___x_2020_, 4, v_defEqCtx_x3f_2003_);
lean_ctor_set(v___x_2020_, 5, v_synthPendingDepth_2004_);
lean_ctor_set(v___x_2020_, 6, v_canUnfold_x3f_2005_);
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*7, v_trackZetaDelta_1999_);
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*7 + 1, v_univApprox_2006_);
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2007_);
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*7 + 3, v_cacheInferType_2008_);
v___x_2021_ = l_Lean_Meta_mkProjection(v_struct_1940_, v___x_2015_, v___x_2020_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec_ref_known(v___x_2020_, 7);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2032_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2032_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2032_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v_a_2022_);
v___x_2027_ = v___x_1946_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_del_object(v___x_1946_);
v_a_2033_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2021_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2021_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
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
lean_object* v_options_2044_; uint8_t v_hasTrace_2045_; 
lean_dec(v___x_1943_);
v_options_2044_ = lean_ctor_get(v___y_1929_, 2);
v_hasTrace_2045_ = lean_ctor_get_uint8(v_options_2044_, sizeof(void*)*1);
if (v_hasTrace_2045_ == 0)
{
goto v___jp_1935_;
}
else
{
lean_object* v_inheritedTraceOptions_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_inheritedTraceOptions_2046_ = lean_ctor_get(v___y_1929_, 13);
v___x_2047_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2048_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_2049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2046_, v_options_2044_, v___x_2048_);
if (v___x_2049_ == 0)
{
goto v___jp_1935_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2050_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__9, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9);
lean_inc(v_typeName_1938_);
v___x_2051_ = l_Lean_MessageData_ofName(v_typeName_1938_);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__11, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__11);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_inc_ref(v_e_1926_);
v___x_2055_ = l_Lean_indentExpr(v_e_1926_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2047_, v___x_2056_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
goto v___jp_1935_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref_known(v_e_1926_, 3);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_e_1926_);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
v___jp_1932_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_e_1926_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
v___jp_1935_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_e_1926_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_e_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_e_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_x_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v_x_2083_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___f_2099_; lean_object* v___x_2100_; 
v___f_2099_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2100_ = lean_find_expr(v___f_2099_, v_e_2093_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_e_2093_);
return v___x_2101_;
}
else
{
lean_object* v_post_2102_; lean_object* v___f_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; 
lean_dec_ref_known(v___x_2100_, 1);
v_post_2102_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v___f_2103_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2104_ = 0;
v___x_2105_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2093_, v___f_2103_, v_post_2102_, v___x_2104_, v___x_2104_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_Meta_Sym_foldProjs(v_e_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
return v_res_2112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2118_ = l_Lean_mkConst(v___x_2117_, v___x_2116_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2124_ = l_Lean_mkConst(v___x_2123_, v___x_2122_);
return v___x_2124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_box(0);
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2132_ = l_Lean_mkConst(v___x_2131_, v___x_2130_);
return v___x_2132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2139_ = l_Lean_mkConst(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = l_Lean_mkNatLit(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2149_ = l_Lean_mkConst(v___x_2148_, v___x_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2153_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2152_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
v_a_2155_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2153_, 2);
v___x_2156_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2157_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2156_, v_a_2150_, v_a_2155_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v_a_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
v_a_2159_ = lean_ctor_get(v___x_2157_, 1);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2157_, 2);
v___x_2160_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2161_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2160_, v_a_2150_, v_a_2159_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
v_a_2163_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2161_, 2);
v___x_2164_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2165_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2164_, v_a_2150_, v_a_2163_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
v_a_2167_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2165_, 2);
v___x_2168_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2169_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2168_, v_a_2150_, v_a_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
v_a_2171_ = lean_ctor_get(v___x_2169_, 1);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2169_, 2);
v___x_2172_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2173_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2172_, v_a_2150_, v_a_2171_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
v_a_2175_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2173_, 2);
v___x_2176_ = l_Lean_Int_mkType;
v___x_2177_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2176_, v_a_2150_, v_a_2175_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2187_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_a_2179_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2181_ = v___x_2177_;
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2183_, 0, v_a_2158_);
lean_ctor_set(v___x_2183_, 1, v_a_2154_);
lean_ctor_set(v___x_2183_, 2, v_a_2170_);
lean_ctor_set(v___x_2183_, 3, v_a_2166_);
lean_ctor_set(v___x_2183_, 4, v_a_2162_);
lean_ctor_set(v___x_2183_, 5, v_a_2174_);
lean_ctor_set(v___x_2183_, 6, v_a_2178_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2183_);
v___x_2185_ = v___x_2181_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_a_2179_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2174_);
lean_dec(v_a_2170_);
lean_dec(v_a_2166_);
lean_dec(v_a_2162_);
lean_dec(v_a_2158_);
lean_dec(v_a_2154_);
v_a_2188_ = lean_ctor_get(v___x_2177_, 0);
v_a_2189_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2177_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_inc(v_a_2188_);
lean_dec(v___x_2177_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2188_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_a_2170_);
lean_dec(v_a_2166_);
lean_dec(v_a_2162_);
lean_dec(v_a_2158_);
lean_dec(v_a_2154_);
v_a_2197_ = lean_ctor_get(v___x_2173_, 0);
v_a_2198_ = lean_ctor_get(v___x_2173_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2173_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_inc(v_a_2197_);
lean_dec(v___x_2173_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2197_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2166_);
lean_dec(v_a_2162_);
lean_dec(v_a_2158_);
lean_dec(v_a_2154_);
v_a_2206_ = lean_ctor_get(v___x_2169_, 0);
v_a_2207_ = lean_ctor_get(v___x_2169_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2169_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_inc(v_a_2206_);
lean_dec(v___x_2169_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2206_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2162_);
lean_dec(v_a_2158_);
lean_dec(v_a_2154_);
v_a_2215_ = lean_ctor_get(v___x_2165_, 0);
v_a_2216_ = lean_ctor_get(v___x_2165_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2165_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_inc(v_a_2215_);
lean_dec(v___x_2165_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2215_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2158_);
lean_dec(v_a_2154_);
v_a_2224_ = lean_ctor_get(v___x_2161_, 0);
v_a_2225_ = lean_ctor_get(v___x_2161_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2161_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_inc(v_a_2224_);
lean_dec(v___x_2161_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2224_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_a_2154_);
v_a_2233_ = lean_ctor_get(v___x_2157_, 0);
v_a_2234_ = lean_ctor_get(v___x_2157_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2157_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_inc(v_a_2233_);
lean_dec(v___x_2157_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2233_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2242_ = lean_ctor_get(v___x_2153_, 0);
v_a_2243_ = lean_ctor_get(v___x_2153_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2153_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_inc(v_a_2242_);
lean_dec(v___x_2153_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2242_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2251_, v_a_2252_);
lean_dec_ref(v_a_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2254_, lean_object* v_opt_2255_){
_start:
{
lean_object* v_name_2256_; lean_object* v_defValue_2257_; lean_object* v_map_2258_; lean_object* v___x_2259_; 
v_name_2256_ = lean_ctor_get(v_opt_2255_, 0);
v_defValue_2257_ = lean_ctor_get(v_opt_2255_, 1);
v_map_2258_ = lean_ctor_get(v_opts_2254_, 0);
v___x_2259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2258_, v_name_2256_);
if (lean_obj_tag(v___x_2259_) == 0)
{
uint8_t v___x_2260_; 
v___x_2260_ = lean_unbox(v_defValue_2257_);
return v___x_2260_;
}
else
{
lean_object* v_val_2261_; 
v_val_2261_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v___x_2259_, 1);
if (lean_obj_tag(v_val_2261_) == 1)
{
uint8_t v_v_2262_; 
v_v_2262_ = lean_ctor_get_uint8(v_val_2261_, 0);
lean_dec_ref_known(v_val_2261_, 0);
return v_v_2262_;
}
else
{
uint8_t v___x_2263_; 
lean_dec(v_val_2261_);
v___x_2263_ = lean_unbox(v_defValue_2257_);
return v___x_2263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2264_, lean_object* v_opt_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2264_, v_opt_2265_);
lean_dec_ref(v_opt_2265_);
lean_dec_ref(v_opts_2264_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___f_2280_; lean_object* v___x_2122__overap_2281_; lean_object* v___x_2282_; 
v___f_2280_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2122__overap_2281_ = lean_panic_fn_borrowed(v___f_2280_, v_msg_2274_);
lean_inc(v___y_2278_);
lean_inc_ref(v___y_2277_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
v___x_2282_ = lean_apply_5(v___x_2122__overap_2281_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, lean_box(0));
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2289_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_box(0));
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2299_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_2300_ = lean_unsigned_to_nat(19u);
v___x_2301_ = lean_unsigned_to_nat(304u);
v___x_2302_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__5));
v___x_2303_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2304_ = l_mkPanicMessageWithDecl(v___x_2303_, v___x_2302_, v___x_2301_, v___x_2300_, v___x_2299_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___x_2353_; lean_object* v_env_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2353_ = lean_st_ref_get(v_a_2309_);
v_env_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref(v_env_2354_);
lean_dec(v___x_2353_);
v___x_2355_ = 0;
v___x_2356_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2356_, 0, v_env_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1, v___x_2355_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1 + 1, v___x_2355_);
v___x_2357_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
v___x_2358_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2356_, v___x_2357_);
lean_dec_ref_known(v___x_2356_, 1);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v_a_2360_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
v_a_2360_ = lean_ctor_get(v___x_2358_, 1);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2358_, 2);
v_fst_2312_ = v_a_2359_;
v_snd_2313_ = v_a_2360_;
v___y_2314_ = v_a_2306_;
v___y_2315_ = v_a_2307_;
v___y_2316_ = v_a_2308_;
v___y_2317_ = v_a_2309_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2358_, 2);
v___x_2361_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__7, &l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7);
v___x_2362_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2361_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_fst_2364_; lean_object* v_snd_2365_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v_fst_2364_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_fst_2364_);
v_snd_2365_ = lean_ctor_get(v_a_2363_, 1);
lean_inc(v_snd_2365_);
lean_dec(v_a_2363_);
v_fst_2312_ = v_fst_2364_;
v_snd_2313_ = v_snd_2365_;
v___y_2314_ = v_a_2306_;
v___y_2315_ = v_a_2307_;
v___y_2316_ = v_a_2308_;
v___y_2317_ = v_a_2309_;
goto v___jp_2311_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v_x_2305_);
v_a_2366_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2362_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
v___jp_2311_:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v_options_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v_options_2320_ = lean_ctor_get(v___y_2316_, 2);
v___x_2321_ = l_Lean_Meta_Sym_sym_debug;
v___x_2322_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_options_2320_, v___x_2321_);
v___x_2323_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2324_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_2327_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v___x_2327_, 0, v_snd_2313_);
lean_ctor_set(v___x_2327_, 1, v___x_2324_);
lean_ctor_set(v___x_2327_, 2, v___x_2324_);
lean_ctor_set(v___x_2327_, 3, v___x_2324_);
lean_ctor_set(v___x_2327_, 4, v___x_2324_);
lean_ctor_set(v___x_2327_, 5, v___x_2324_);
lean_ctor_set(v___x_2327_, 6, v___x_2324_);
lean_ctor_set(v___x_2327_, 7, v_a_2319_);
lean_ctor_set(v___x_2327_, 8, v___x_2325_);
lean_ctor_set(v___x_2327_, 9, v___x_2326_);
lean_ctor_set(v___x_2327_, 10, v___x_2324_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*11, v___x_2322_);
v___x_2328_ = lean_st_mk_ref(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_fst_2312_);
lean_ctor_set(v___x_2329_, 1, v___x_2323_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc(v___x_2328_);
v___x_2330_ = lean_apply_7(v_x_2305_, v___x_2329_, v___x_2328_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, lean_box(0));
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2339_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = lean_st_ref_get(v___x_2328_);
lean_dec(v___x_2328_);
lean_dec(v___x_2335_);
if (v_isShared_2334_ == 0)
{
v___x_2337_ = v___x_2333_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2331_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
lean_dec(v___x_2328_);
return v___x_2330_;
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_snd_2313_);
lean_dec_ref(v_fst_2312_);
lean_dec_ref(v_x_2305_);
v_a_2340_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2342_ = v___x_2318_;
v_isShared_2343_ = v_isSharedCheck_2352_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2318_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2352_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_ref_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v_ref_2344_ = lean_ctor_get(v___y_2316_, 5);
v___x_2345_ = lean_io_error_to_string(v_a_2340_);
v___x_2346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
v___x_2347_ = l_Lean_MessageData_ofFormat(v___x_2346_);
lean_inc(v_ref_2344_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_ref_2344_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2348_);
v___x_2350_ = v___x_2342_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2381_, lean_object* v_x_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_x_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2389_, v_x_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2397_){
_start:
{
lean_object* v_sharedExprs_2399_; lean_object* v___x_2400_; 
v_sharedExprs_2399_ = lean_ctor_get(v_a_2397_, 0);
lean_inc_ref(v_sharedExprs_2399_);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_sharedExprs_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2401_);
lean_dec_ref(v_a_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2404_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
v___x_2422_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2420_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_trueExpr_2427_; lean_object* v___x_2429_; 
v_trueExpr_2427_ = lean_ctor_get(v_a_2423_, 0);
lean_inc_ref(v_trueExpr_2427_);
lean_dec(v_a_2423_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v_trueExpr_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_trueExpr_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2432_);
lean_dec_ref(v_a_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2435_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2466_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2466_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2466_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
size_t v___x_2459_; size_t v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2459_ = lean_ptr_addr(v_e_2451_);
v___x_2460_ = lean_ptr_addr(v_a_2455_);
lean_dec(v_a_2455_);
v___x_2461_ = lean_usize_dec_eq(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_box(v___x_2461_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2462_);
v___x_2464_ = v___x_2457_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2454_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2454_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2475_, v_a_2476_);
lean_dec_ref(v_a_2476_);
lean_dec_ref(v_e_2475_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2479_, v_a_2480_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec_ref(v_e_2488_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2508_; 
v___x_2499_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2497_);
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_falseExpr_2504_; lean_object* v___x_2506_; 
v_falseExpr_2504_ = lean_ctor_get(v_a_2500_, 1);
lean_inc_ref(v_falseExpr_2504_);
lean_dec(v_a_2500_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v_falseExpr_2504_);
v___x_2506_ = v___x_2502_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_falseExpr_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2509_);
lean_dec_ref(v_a_2509_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2512_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2543_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2543_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2543_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
size_t v___x_2536_; size_t v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2536_ = lean_ptr_addr(v_e_2528_);
v___x_2537_ = lean_ptr_addr(v_a_2532_);
lean_dec(v_a_2532_);
v___x_2538_ = lean_usize_dec_eq(v___x_2536_, v___x_2537_);
v___x_2539_ = lean_box(v___x_2538_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2539_);
v___x_2541_ = v___x_2534_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2531_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2531_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2552_, v_a_2553_);
lean_dec_ref(v_a_2553_);
lean_dec_ref(v_e_2552_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2556_, v_a_2557_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec_ref(v_e_2565_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2576_; lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
v___x_2576_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2574_);
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v_btrueExpr_2581_; lean_object* v___x_2583_; 
v_btrueExpr_2581_ = lean_ctor_get(v_a_2577_, 3);
lean_inc_ref(v_btrueExpr_2581_);
lean_dec(v_a_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_btrueExpr_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_btrueExpr_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2586_);
lean_dec_ref(v_a_2586_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2589_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2606_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2620_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2620_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2620_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
size_t v___x_2613_; size_t v___x_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2613_ = lean_ptr_addr(v_e_2605_);
v___x_2614_ = lean_ptr_addr(v_a_2609_);
lean_dec(v_a_2609_);
v___x_2615_ = lean_usize_dec_eq(v___x_2613_, v___x_2614_);
v___x_2616_ = lean_box(v___x_2615_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2616_);
v___x_2618_ = v___x_2611_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_a_2621_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2608_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2608_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2629_, v_a_2630_);
lean_dec_ref(v_a_2630_);
lean_dec_ref(v_e_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2633_, v_a_2634_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec_ref(v_e_2642_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v___x_2653_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2651_);
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_bfalseExpr_2658_; lean_object* v___x_2660_; 
v_bfalseExpr_2658_ = lean_ctor_get(v_a_2654_, 4);
lean_inc_ref(v_bfalseExpr_2658_);
lean_dec(v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_bfalseExpr_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_bfalseExpr_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2663_);
lean_dec_ref(v_a_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2666_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2683_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2697_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
size_t v___x_2690_; size_t v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2690_ = lean_ptr_addr(v_e_2682_);
v___x_2691_ = lean_ptr_addr(v_a_2686_);
lean_dec(v_a_2686_);
v___x_2692_ = lean_usize_dec_eq(v___x_2690_, v___x_2691_);
v___x_2693_ = lean_box(v___x_2692_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2693_);
v___x_2695_ = v___x_2688_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v_a_2698_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2685_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2685_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2706_, v_a_2707_);
lean_dec_ref(v_a_2707_);
lean_dec_ref(v_e_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2710_, v_a_2711_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec_ref(v_e_2719_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2739_; 
v___x_2730_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2728_);
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_natZExpr_2735_; lean_object* v___x_2737_; 
v_natZExpr_2735_ = lean_ctor_get(v_a_2731_, 2);
lean_inc_ref(v_natZExpr_2735_);
lean_dec(v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_natZExpr_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_natZExpr_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2740_);
lean_dec_ref(v_a_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2743_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2770_; 
v___x_2761_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2759_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_ordEqExpr_2766_; lean_object* v___x_2768_; 
v_ordEqExpr_2766_ = lean_ctor_get(v_a_2762_, 5);
lean_inc_ref(v_ordEqExpr_2766_);
lean_dec(v_a_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_ordEqExpr_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_ordEqExpr_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2771_);
lean_dec_ref(v_a_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2774_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2790_){
_start:
{
lean_object* v___x_2792_; lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2801_; 
v___x_2792_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2790_);
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v_intExpr_2797_; lean_object* v___x_2799_; 
v_intExpr_2797_ = lean_ctor_get(v_a_2793_, 6);
lean_inc_ref(v_intExpr_2797_);
lean_dec(v_a_2793_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_intExpr_2797_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_intExpr_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2802_);
lean_dec_ref(v_a_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2805_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Meta_Sym_getIntExpr(v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2821_, lean_object* v_ctx_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v_share_2826_; lean_object* v_maxFVar_2827_; lean_object* v_proofInstInfo_2828_; lean_object* v_inferType_2829_; lean_object* v_getLevel_2830_; lean_object* v_congrInfo_2831_; lean_object* v_defEqI_2832_; lean_object* v_extensions_2833_; lean_object* v_issues_2834_; lean_object* v_canon_2835_; lean_object* v_instanceOverrides_2836_; uint8_t v_debug_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2897_; 
v___x_2825_ = lean_st_ref_take(v_a_2823_);
v_share_2826_ = lean_ctor_get(v___x_2825_, 0);
v_maxFVar_2827_ = lean_ctor_get(v___x_2825_, 1);
v_proofInstInfo_2828_ = lean_ctor_get(v___x_2825_, 2);
v_inferType_2829_ = lean_ctor_get(v___x_2825_, 3);
v_getLevel_2830_ = lean_ctor_get(v___x_2825_, 4);
v_congrInfo_2831_ = lean_ctor_get(v___x_2825_, 5);
v_defEqI_2832_ = lean_ctor_get(v___x_2825_, 6);
v_extensions_2833_ = lean_ctor_get(v___x_2825_, 7);
v_issues_2834_ = lean_ctor_get(v___x_2825_, 8);
v_canon_2835_ = lean_ctor_get(v___x_2825_, 9);
v_instanceOverrides_2836_ = lean_ctor_get(v___x_2825_, 10);
v_debug_2837_ = lean_ctor_get_uint8(v___x_2825_, sizeof(void*)*11);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2839_ = v___x_2825_;
v_isShared_2840_ = v_isSharedCheck_2897_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_instanceOverrides_2836_);
lean_inc(v_canon_2835_);
lean_inc(v_issues_2834_);
lean_inc(v_extensions_2833_);
lean_inc(v_defEqI_2832_);
lean_inc(v_congrInfo_2831_);
lean_inc(v_getLevel_2830_);
lean_inc(v_inferType_2829_);
lean_inc(v_proofInstInfo_2828_);
lean_inc(v_maxFVar_2827_);
lean_inc(v_share_2826_);
lean_dec(v___x_2825_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2897_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2841_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2841_);
v___x_2843_ = v___x_2839_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_maxFVar_2827_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_proofInstInfo_2828_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_inferType_2829_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_getLevel_2830_);
lean_ctor_set(v_reuseFailAlloc_2896_, 5, v_congrInfo_2831_);
lean_ctor_set(v_reuseFailAlloc_2896_, 6, v_defEqI_2832_);
lean_ctor_set(v_reuseFailAlloc_2896_, 7, v_extensions_2833_);
lean_ctor_set(v_reuseFailAlloc_2896_, 8, v_issues_2834_);
lean_ctor_set(v_reuseFailAlloc_2896_, 9, v_canon_2835_);
lean_ctor_set(v_reuseFailAlloc_2896_, 10, v_instanceOverrides_2836_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*11, v_debug_2837_);
v___x_2843_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = lean_st_ref_set(v_a_2823_, v___x_2843_);
v___x_2845_ = lean_apply_2(v_k_2821_, v_ctx_2822_, v_share_2826_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v_maxFVar_2849_; lean_object* v_proofInstInfo_2850_; lean_object* v_inferType_2851_; lean_object* v_getLevel_2852_; lean_object* v_congrInfo_2853_; lean_object* v_defEqI_2854_; lean_object* v_extensions_2855_; lean_object* v_issues_2856_; lean_object* v_canon_2857_; lean_object* v_instanceOverrides_2858_; uint8_t v_debug_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2869_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
v_a_2847_ = lean_ctor_get(v___x_2845_, 1);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2845_, 2);
v___x_2848_ = lean_st_ref_take(v_a_2823_);
v_maxFVar_2849_ = lean_ctor_get(v___x_2848_, 1);
v_proofInstInfo_2850_ = lean_ctor_get(v___x_2848_, 2);
v_inferType_2851_ = lean_ctor_get(v___x_2848_, 3);
v_getLevel_2852_ = lean_ctor_get(v___x_2848_, 4);
v_congrInfo_2853_ = lean_ctor_get(v___x_2848_, 5);
v_defEqI_2854_ = lean_ctor_get(v___x_2848_, 6);
v_extensions_2855_ = lean_ctor_get(v___x_2848_, 7);
v_issues_2856_ = lean_ctor_get(v___x_2848_, 8);
v_canon_2857_ = lean_ctor_get(v___x_2848_, 9);
v_instanceOverrides_2858_ = lean_ctor_get(v___x_2848_, 10);
v_debug_2859_ = lean_ctor_get_uint8(v___x_2848_, sizeof(void*)*11);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v___x_2848_, 0);
lean_dec(v_unused_2870_);
v___x_2861_ = v___x_2848_;
v_isShared_2862_ = v_isSharedCheck_2869_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_instanceOverrides_2858_);
lean_inc(v_canon_2857_);
lean_inc(v_issues_2856_);
lean_inc(v_extensions_2855_);
lean_inc(v_defEqI_2854_);
lean_inc(v_congrInfo_2853_);
lean_inc(v_getLevel_2852_);
lean_inc(v_inferType_2851_);
lean_inc(v_proofInstInfo_2850_);
lean_inc(v_maxFVar_2849_);
lean_dec(v___x_2848_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2869_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v_a_2847_);
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2847_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_maxFVar_2849_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_proofInstInfo_2850_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_inferType_2851_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_getLevel_2852_);
lean_ctor_set(v_reuseFailAlloc_2868_, 5, v_congrInfo_2853_);
lean_ctor_set(v_reuseFailAlloc_2868_, 6, v_defEqI_2854_);
lean_ctor_set(v_reuseFailAlloc_2868_, 7, v_extensions_2855_);
lean_ctor_set(v_reuseFailAlloc_2868_, 8, v_issues_2856_);
lean_ctor_set(v_reuseFailAlloc_2868_, 9, v_canon_2857_);
lean_ctor_set(v_reuseFailAlloc_2868_, 10, v_instanceOverrides_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*11, v_debug_2859_);
v___x_2864_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_st_ref_set(v_a_2823_, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_a_2846_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v_maxFVar_2874_; lean_object* v_proofInstInfo_2875_; lean_object* v_inferType_2876_; lean_object* v_getLevel_2877_; lean_object* v_congrInfo_2878_; lean_object* v_defEqI_2879_; lean_object* v_extensions_2880_; lean_object* v_issues_2881_; lean_object* v_canon_2882_; lean_object* v_instanceOverrides_2883_; uint8_t v_debug_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2894_; 
v_a_2871_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2871_);
v_a_2872_ = lean_ctor_get(v___x_2845_, 1);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2845_, 2);
v___x_2873_ = lean_st_ref_take(v_a_2823_);
v_maxFVar_2874_ = lean_ctor_get(v___x_2873_, 1);
v_proofInstInfo_2875_ = lean_ctor_get(v___x_2873_, 2);
v_inferType_2876_ = lean_ctor_get(v___x_2873_, 3);
v_getLevel_2877_ = lean_ctor_get(v___x_2873_, 4);
v_congrInfo_2878_ = lean_ctor_get(v___x_2873_, 5);
v_defEqI_2879_ = lean_ctor_get(v___x_2873_, 6);
v_extensions_2880_ = lean_ctor_get(v___x_2873_, 7);
v_issues_2881_ = lean_ctor_get(v___x_2873_, 8);
v_canon_2882_ = lean_ctor_get(v___x_2873_, 9);
v_instanceOverrides_2883_ = lean_ctor_get(v___x_2873_, 10);
v_debug_2884_ = lean_ctor_get_uint8(v___x_2873_, sizeof(void*)*11);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2895_);
v___x_2886_ = v___x_2873_;
v_isShared_2887_ = v_isSharedCheck_2894_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_instanceOverrides_2883_);
lean_inc(v_canon_2882_);
lean_inc(v_issues_2881_);
lean_inc(v_extensions_2880_);
lean_inc(v_defEqI_2879_);
lean_inc(v_congrInfo_2878_);
lean_inc(v_getLevel_2877_);
lean_inc(v_inferType_2876_);
lean_inc(v_proofInstInfo_2875_);
lean_inc(v_maxFVar_2874_);
lean_dec(v___x_2873_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2894_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_a_2872_);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2872_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_maxFVar_2874_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_proofInstInfo_2875_);
lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_inferType_2876_);
lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_getLevel_2877_);
lean_ctor_set(v_reuseFailAlloc_2893_, 5, v_congrInfo_2878_);
lean_ctor_set(v_reuseFailAlloc_2893_, 6, v_defEqI_2879_);
lean_ctor_set(v_reuseFailAlloc_2893_, 7, v_extensions_2880_);
lean_ctor_set(v_reuseFailAlloc_2893_, 8, v_issues_2881_);
lean_ctor_set(v_reuseFailAlloc_2893_, 9, v_canon_2882_);
lean_ctor_set(v_reuseFailAlloc_2893_, 10, v_instanceOverrides_2883_);
lean_ctor_set_uint8(v_reuseFailAlloc_2893_, sizeof(void*)*11, v_debug_2884_);
v___x_2889_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_st_ref_set(v_a_2823_, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_a_2871_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2898_, lean_object* v_ctx_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2898_, v_ctx_2899_, v_a_2900_);
lean_dec(v_a_2900_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2903_, lean_object* v_k_2904_, lean_object* v_ctx_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2904_, v_ctx_2905_, v_a_2907_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_k_2915_, lean_object* v_ctx_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2914_, v_k_2915_, v_ctx_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2925_){
_start:
{
lean_object* v_config_2926_; lean_object* v_sharedExprs_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2944_; 
v_config_2926_ = lean_ctor_get(v_ctx_2925_, 1);
v_sharedExprs_2927_ = lean_ctor_get(v_ctx_2925_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_ctx_2925_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2929_ = v_ctx_2925_;
v_isShared_2930_ = v_isSharedCheck_2944_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_config_2926_);
lean_inc(v_sharedExprs_2927_);
lean_dec(v_ctx_2925_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2944_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
uint8_t v_verbose_2931_; uint8_t v_enforceUnfoldReducible_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2943_; 
v_verbose_2931_ = lean_ctor_get_uint8(v_config_2926_, 0);
v_enforceUnfoldReducible_2932_ = lean_ctor_get_uint8(v_config_2926_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_config_2926_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2934_ = v_config_2926_;
v_isShared_2935_ = v_isSharedCheck_2943_;
goto v_resetjp_2933_;
}
else
{
lean_dec(v_config_2926_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2943_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
uint8_t v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = 0;
if (v_isShared_2935_ == 0)
{
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2942_, 0, v_verbose_2931_);
lean_ctor_set_uint8(v_reuseFailAlloc_2942_, 1, v_enforceUnfoldReducible_2932_);
v___x_2938_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2940_; 
lean_ctor_set_uint8(v___x_2938_, 2, v___x_2936_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_2938_);
v___x_2940_ = v___x_2929_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_sharedExprs_2927_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2946_, lean_object* v_x_2947_){
_start:
{
lean_object* v___f_2948_; lean_object* v___x_2949_; 
v___f_2948_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2949_ = lean_apply_3(v_inst_2946_, lean_box(0), v___f_2948_, v_x_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2950_, lean_object* v_00_u03b1_2951_, lean_object* v_inst_2952_, lean_object* v_x_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2952_, v_x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2955_){
_start:
{
lean_object* v_config_2956_; lean_object* v_sharedExprs_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2973_; 
v_config_2956_ = lean_ctor_get(v_ctx_2955_, 1);
v_sharedExprs_2957_ = lean_ctor_get(v_ctx_2955_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_ctx_2955_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2959_ = v_ctx_2955_;
v_isShared_2960_ = v_isSharedCheck_2973_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_config_2956_);
lean_inc(v_sharedExprs_2957_);
lean_dec(v_ctx_2955_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2973_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
uint8_t v_verbose_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2972_; 
v_verbose_2961_ = lean_ctor_get_uint8(v_config_2956_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_config_2956_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2963_ = v_config_2956_;
v_isShared_2964_ = v_isSharedCheck_2972_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v_config_2956_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2972_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
uint8_t v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = 0;
if (v_isShared_2964_ == 0)
{
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2971_, 0, v_verbose_2961_);
v___x_2967_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
lean_ctor_set_uint8(v___x_2967_, 1, v___x_2965_);
lean_ctor_set_uint8(v___x_2967_, 2, v___x_2965_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_2967_);
v___x_2969_ = v___x_2959_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_sharedExprs_2957_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_2975_, lean_object* v_x_2976_){
_start:
{
lean_object* v___f_2977_; lean_object* v___x_2978_; 
v___f_2977_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_2978_ = lean_apply_3(v_inst_2975_, lean_box(0), v___f_2977_, v_x_2976_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_2979_, lean_object* v_00_u03b1_2980_, lean_object* v_inst_2981_, lean_object* v_x_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_2981_, v_x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v_config_2988_; lean_object* v_env_2989_; uint8_t v_enforceUnfoldReducible_2990_; uint8_t v_enforceFoldProjs_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2987_ = lean_st_ref_get(v_a_2985_);
v_config_2988_ = lean_ctor_get(v_a_2984_, 1);
v_env_2989_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_ref(v_env_2989_);
lean_dec(v___x_2987_);
v_enforceUnfoldReducible_2990_ = lean_ctor_get_uint8(v_config_2988_, 1);
v_enforceFoldProjs_2991_ = lean_ctor_get_uint8(v_config_2988_, 2);
v___x_2992_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2992_, 0, v_env_2989_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*1, v_enforceUnfoldReducible_2990_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*1 + 1, v_enforceFoldProjs_2991_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2998_, v_a_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_config_3021_; uint8_t v_enforceUnfoldReducible_3022_; uint8_t v_enforceFoldProjs_3023_; lean_object* v_e_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v_e_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; 
v_config_3021_ = lean_ctor_get(v_a_3015_, 1);
v_enforceUnfoldReducible_3022_ = lean_ctor_get_uint8(v_config_3021_, 1);
v_enforceFoldProjs_3023_ = lean_ctor_get_uint8(v_config_3021_, 2);
if (v_enforceUnfoldReducible_3022_ == 0)
{
v_e_3033_ = v_e_3014_;
v___y_3034_ = v_a_3016_;
v___y_3035_ = v_a_3017_;
v___y_3036_ = v_a_3018_;
v___y_3037_ = v_a_3019_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3014_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v_e_3033_ = v_a_3041_;
v___y_3034_ = v_a_3016_;
v___y_3035_ = v_a_3017_;
v___y_3036_ = v_a_3018_;
v___y_3037_ = v_a_3019_;
goto v___jp_3032_;
}
else
{
return v___x_3040_;
}
}
v___jp_3024_:
{
if (v_enforceUnfoldReducible_3022_ == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_e_3025_);
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
return v___x_3031_;
}
}
v___jp_3032_:
{
if (v_enforceFoldProjs_3023_ == 0)
{
v_e_3025_ = v_e_3033_;
v___y_3026_ = v___y_3034_;
v___y_3027_ = v___y_3035_;
v___y_3028_ = v___y_3036_;
v___y_3029_ = v___y_3037_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_Meta_Sym_foldProjs(v_e_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v_e_3025_ = v_a_3039_;
v___y_3026_ = v___y_3034_;
v___y_3027_ = v___y_3035_;
v___y_3028_ = v___y_3036_;
v___y_3029_ = v___y_3037_;
goto v___jp_3024_;
}
else
{
return v___x_3038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec_ref(v_a_3043_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3050_, v_a_3051_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
return v_res_3067_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_instMonadEIO(lean_box(0));
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_toApplicative_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3146_; 
v___x_3081_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3082_ = l_StateRefT_x27_instMonad___redArg(v___x_3081_);
v_toApplicative_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_3082_, 1);
lean_dec(v_unused_3147_);
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3146_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_toApplicative_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3146_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v_toFunctor_3087_; lean_object* v_toSeq_3088_; lean_object* v_toSeqLeft_3089_; lean_object* v_toSeqRight_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3144_; 
v_toFunctor_3087_ = lean_ctor_get(v_toApplicative_3083_, 0);
v_toSeq_3088_ = lean_ctor_get(v_toApplicative_3083_, 2);
v_toSeqLeft_3089_ = lean_ctor_get(v_toApplicative_3083_, 3);
v_toSeqRight_3090_ = lean_ctor_get(v_toApplicative_3083_, 4);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_toApplicative_3083_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v_toApplicative_3083_, 1);
lean_dec(v_unused_3145_);
v___x_3092_ = v_toApplicative_3083_;
v_isShared_3093_ = v_isSharedCheck_3144_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_toSeqRight_3090_);
lean_inc(v_toSeqLeft_3089_);
lean_inc(v_toSeq_3088_);
lean_inc(v_toFunctor_3087_);
lean_dec(v_toApplicative_3083_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3144_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___f_3094_; lean_object* v___f_3095_; lean_object* v___f_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___f_3100_; lean_object* v___f_3101_; lean_object* v___x_3103_; 
v___f_3094_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3095_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3087_);
v___f_3096_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3096_, 0, v_toFunctor_3087_);
v___f_3097_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3097_, 0, v_toFunctor_3087_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___f_3096_);
lean_ctor_set(v___x_3098_, 1, v___f_3097_);
v___f_3099_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3099_, 0, v_toSeqRight_3090_);
v___f_3100_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3100_, 0, v_toSeqLeft_3089_);
v___f_3101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3101_, 0, v_toSeq_3088_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v___f_3099_);
lean_ctor_set(v___x_3092_, 3, v___f_3100_);
lean_ctor_set(v___x_3092_, 2, v___f_3101_);
lean_ctor_set(v___x_3092_, 1, v___f_3094_);
lean_ctor_set(v___x_3092_, 0, v___x_3098_);
v___x_3103_ = v___x_3092_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___f_3094_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v___f_3101_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v___f_3100_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v___f_3099_);
v___x_3103_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3105_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v___f_3095_);
lean_ctor_set(v___x_3085_, 0, v___x_3103_);
v___x_3105_ = v___x_3085_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___f_3095_);
v___x_3105_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v_toApplicative_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3140_; 
v___x_3106_ = l_StateRefT_x27_instMonad___redArg(v___x_3105_);
v_toApplicative_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3106_, 1);
lean_dec(v_unused_3141_);
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3140_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_toApplicative_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3140_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_toFunctor_3111_; lean_object* v_toSeq_3112_; lean_object* v_toSeqLeft_3113_; lean_object* v_toSeqRight_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3138_; 
v_toFunctor_3111_ = lean_ctor_get(v_toApplicative_3107_, 0);
v_toSeq_3112_ = lean_ctor_get(v_toApplicative_3107_, 2);
v_toSeqLeft_3113_ = lean_ctor_get(v_toApplicative_3107_, 3);
v_toSeqRight_3114_ = lean_ctor_get(v_toApplicative_3107_, 4);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_toApplicative_3107_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v_toApplicative_3107_, 1);
lean_dec(v_unused_3139_);
v___x_3116_ = v_toApplicative_3107_;
v_isShared_3117_ = v_isSharedCheck_3138_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_toSeqRight_3114_);
lean_inc(v_toSeqLeft_3113_);
lean_inc(v_toSeq_3112_);
lean_inc(v_toFunctor_3111_);
lean_dec(v_toApplicative_3107_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3138_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___f_3118_; lean_object* v___f_3119_; lean_object* v___f_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___f_3125_; lean_object* v___x_3127_; 
v___f_3118_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3119_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3111_);
v___f_3120_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3120_, 0, v_toFunctor_3111_);
v___f_3121_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3121_, 0, v_toFunctor_3111_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___f_3120_);
lean_ctor_set(v___x_3122_, 1, v___f_3121_);
v___f_3123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3123_, 0, v_toSeqRight_3114_);
v___f_3124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3124_, 0, v_toSeqLeft_3113_);
v___f_3125_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3125_, 0, v_toSeq_3112_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 4, v___f_3123_);
lean_ctor_set(v___x_3116_, 3, v___f_3124_);
lean_ctor_set(v___x_3116_, 2, v___f_3125_);
lean_ctor_set(v___x_3116_, 1, v___f_3118_);
lean_ctor_set(v___x_3116_, 0, v___x_3122_);
v___x_3127_ = v___x_3116_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___f_3118_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v___f_3125_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v___f_3124_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v___f_3123_);
v___x_3127_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3129_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___f_3119_);
lean_ctor_set(v___x_3109_, 0, v___x_3127_);
v___x_3129_ = v___x_3109_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___f_3119_);
v___x_3129_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___f_3133_; lean_object* v___x_909__overap_3134_; lean_object* v___x_3135_; 
v___x_3130_ = l_StateRefT_x27_instMonad___redArg(v___x_3129_);
v___x_3131_ = l_Lean_instInhabitedExpr;
v___x_3132_ = l_instInhabitedOfMonad___redArg(v___x_3130_, v___x_3131_);
v___f_3133_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3133_, 0, v___x_3132_);
v___x_909__overap_3134_ = lean_panic_fn_borrowed(v___f_3133_, v_msg_3073_);
lean_dec_ref(v___f_3133_);
lean_inc(v___y_3079_);
lean_inc_ref(v___y_3078_);
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
v___x_3135_ = lean_apply_7(v___x_909__overap_3134_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, lean_box(0));
return v___x_3135_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3157_, lean_object* v_vals_3158_, lean_object* v_i_3159_, lean_object* v_k_3160_){
_start:
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = lean_array_get_size(v_keys_3157_);
v___x_3162_ = lean_nat_dec_lt(v_i_3159_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_dec(v_i_3159_);
v___x_3163_ = lean_box(0);
return v___x_3163_;
}
else
{
lean_object* v_k_x27_3164_; uint8_t v___x_3165_; 
v_k_x27_3164_ = lean_array_fget_borrowed(v_keys_3157_, v_i_3159_);
v___x_3165_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3160_, v_k_x27_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_unsigned_to_nat(1u);
v___x_3167_ = lean_nat_add(v_i_3159_, v___x_3166_);
lean_dec(v_i_3159_);
v_i_3159_ = v___x_3167_;
goto _start;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_array_fget_borrowed(v_vals_3158_, v_i_3159_);
lean_dec(v_i_3159_);
lean_inc(v___x_3169_);
lean_inc(v_k_x27_3164_);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_k_x27_3164_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3172_, lean_object* v_vals_3173_, lean_object* v_i_3174_, lean_object* v_k_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3172_, v_vals_3173_, v_i_3174_, v_k_3175_);
lean_dec_ref(v_k_3175_);
lean_dec_ref(v_vals_3173_);
lean_dec_ref(v_keys_3172_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3177_, size_t v_x_3178_, lean_object* v_x_3179_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 0)
{
lean_object* v_es_3180_; lean_object* v___x_3181_; size_t v___x_3182_; size_t v___x_3183_; lean_object* v_j_3184_; lean_object* v___x_3185_; 
v_es_3180_ = lean_ctor_get(v_x_3177_, 0);
v___x_3181_ = lean_box(2);
v___x_3182_ = ((size_t)31ULL);
v___x_3183_ = lean_usize_land(v_x_3178_, v___x_3182_);
v_j_3184_ = lean_usize_to_nat(v___x_3183_);
v___x_3185_ = lean_array_get_borrowed(v___x_3181_, v_es_3180_, v_j_3184_);
lean_dec(v_j_3184_);
switch(lean_obj_tag(v___x_3185_))
{
case 0:
{
lean_object* v_key_3186_; lean_object* v_val_3187_; uint8_t v___x_3188_; 
v_key_3186_ = lean_ctor_get(v___x_3185_, 0);
v_val_3187_ = lean_ctor_get(v___x_3185_, 1);
v___x_3188_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3179_, v_key_3186_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_box(0);
return v___x_3189_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_inc(v_val_3187_);
lean_inc(v_key_3186_);
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v_key_3186_);
lean_ctor_set(v___x_3190_, 1, v_val_3187_);
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
case 1:
{
lean_object* v_node_3192_; size_t v___x_3193_; size_t v___x_3194_; 
v_node_3192_ = lean_ctor_get(v___x_3185_, 0);
v___x_3193_ = ((size_t)5ULL);
v___x_3194_ = lean_usize_shift_right(v_x_3178_, v___x_3193_);
v_x_3177_ = v_node_3192_;
v_x_3178_ = v___x_3194_;
goto _start;
}
default: 
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_box(0);
return v___x_3196_;
}
}
}
else
{
lean_object* v_ks_3197_; lean_object* v_vs_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_ks_3197_ = lean_ctor_get(v_x_3177_, 0);
v_vs_3198_ = lean_ctor_get(v_x_3177_, 1);
v___x_3199_ = lean_unsigned_to_nat(0u);
v___x_3200_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3197_, v_vs_3198_, v___x_3199_, v_x_3179_);
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
size_t v_x_1226__boxed_3204_; lean_object* v_res_3205_; 
v_x_1226__boxed_3204_ = lean_unbox_usize(v_x_3202_);
lean_dec(v_x_3202_);
v_res_3205_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3201_, v_x_1226__boxed_3204_, v_x_3203_);
lean_dec_ref(v_x_3203_);
lean_dec_ref(v_x_3201_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
uint64_t v___x_3208_; size_t v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3207_);
v___x_3209_ = lean_uint64_to_usize(v___x_3208_);
v___x_3210_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3206_, v___x_3209_, v_x_3207_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3211_, v_x_3212_);
lean_dec_ref(v_x_3212_);
lean_dec_ref(v_x_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3214_, lean_object* v_cache_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3217_, v_e_3214_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_cache_3215_);
lean_ctor_set(v___x_3219_, 1, v___y_3217_);
v___x_3220_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3214_, v___y_3216_, v___x_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3230_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 1);
v_a_3222_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3224_ = v___x_3220_;
v_isShared_3225_ = v_isSharedCheck_3230_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3221_);
lean_inc(v_a_3222_);
lean_dec(v___x_3220_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3230_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v_set_3226_; lean_object* v___x_3228_; 
v_set_3226_ = lean_ctor_get(v_a_3221_, 1);
lean_inc_ref(v_set_3226_);
lean_dec(v_a_3221_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v_set_3226_);
v___x_3228_ = v___x_3224_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3222_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_set_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3240_; 
v_a_3231_ = lean_ctor_get(v___x_3220_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v___x_3220_, 0);
lean_dec(v_unused_3241_);
v___x_3233_ = v___x_3220_;
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3220_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_map_3235_; lean_object* v_set_3236_; lean_object* v___x_3238_; 
v_map_3235_ = lean_ctor_get(v_a_3231_, 0);
lean_inc_ref(v_map_3235_);
v_set_3236_ = lean_ctor_get(v_a_3231_, 1);
lean_inc_ref(v_set_3236_);
lean_dec(v_a_3231_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v_set_3236_);
lean_ctor_set(v___x_3233_, 0, v_map_3235_);
v___x_3238_ = v___x_3233_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_map_3235_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_set_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_val_3242_; lean_object* v_fst_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_cache_3215_);
lean_dec_ref(v_e_3214_);
v_val_3242_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3242_);
lean_dec_ref_known(v___x_3218_, 1);
v_fst_3243_ = lean_ctor_get(v_val_3242_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_val_3242_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_val_3242_, 1);
lean_dec(v_unused_3251_);
v___x_3245_ = v_val_3242_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_fst_3243_);
lean_dec(v_val_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 1, v___y_3217_);
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_fst_3243_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___y_3217_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3252_, lean_object* v_cache_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3252_, v_cache_3253_, v___y_3254_, v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3256_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3258_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_3259_ = lean_unsigned_to_nat(16u);
v___x_3260_ = lean_unsigned_to_nat(396u);
v___x_3261_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3262_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3263_ = l_mkPanicMessageWithDecl(v___x_3262_, v___x_3261_, v___x_3260_, v___x_3259_, v___x_3258_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3264_, lean_object* v_cache_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v_env_3274_; lean_object* v___f_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3289_; 
v___x_3273_ = lean_st_ref_get(v_a_3271_);
v_env_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc_ref(v_env_3274_);
lean_dec(v___x_3273_);
v___f_3275_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3275_, 0, v_e_3264_);
lean_closure_set(v___f_3275_, 1, v_cache_3265_);
v___x_3276_ = 0;
v___x_3277_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3277_, 0, v_env_3274_);
lean_ctor_set_uint8(v___x_3277_, sizeof(void*)*1, v___x_3276_);
lean_ctor_set_uint8(v___x_3277_, sizeof(void*)*1 + 1, v___x_3276_);
v___x_3278_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3275_, v___x_3277_, v_a_3267_);
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
if (lean_obj_tag(v_a_3279_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec_ref_known(v_a_3279_, 1);
lean_del_object(v___x_3281_);
v___x_3283_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3284_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3283_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3284_;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; 
v_a_3285_ = lean_ctor_get(v_a_3279_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v_a_3279_, 1);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v_a_3285_);
v___x_3287_ = v___x_3281_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3290_, lean_object* v_cache_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3290_, v_cache_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3301_, v_x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3304_, v_x_3305_, v_x_3306_);
lean_dec_ref(v_x_3306_);
lean_dec_ref(v_x_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3308_, lean_object* v_x_3309_, size_t v_x_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3309_, v_x_3310_, v_x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
size_t v_x_1431__boxed_3317_; lean_object* v_res_3318_; 
v_x_1431__boxed_3317_ = lean_unbox_usize(v_x_3315_);
lean_dec(v_x_3315_);
v_res_3318_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3313_, v_x_3314_, v_x_1431__boxed_3317_, v_x_3316_);
lean_dec_ref(v_x_3316_);
lean_dec_ref(v_x_3314_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3319_, lean_object* v_keys_3320_, lean_object* v_vals_3321_, lean_object* v_heq_3322_, lean_object* v_i_3323_, lean_object* v_k_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3320_, v_vals_3321_, v_i_3323_, v_k_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3326_, lean_object* v_keys_3327_, lean_object* v_vals_3328_, lean_object* v_heq_3329_, lean_object* v_i_3330_, lean_object* v_k_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3326_, v_keys_3327_, v_vals_3328_, v_heq_3329_, v_i_3330_, v_k_3331_);
lean_dec_ref(v_k_3331_);
lean_dec_ref(v_vals_3328_);
lean_dec_ref(v_keys_3327_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_ref_3339_; lean_object* v___x_3340_; lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3349_; 
v_ref_3339_ = lean_ctor_get(v___y_3336_, 5);
v___x_3340_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
lean_inc(v_ref_3339_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_ref_3339_);
lean_ctor_set(v___x_3345_, 1, v_a_3341_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 1);
lean_ctor_set(v___x_3343_, 0, v___x_3345_);
v___x_3347_ = v___x_3343_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3359_ = l_Lean_stringToMessageData(v___x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3360_, lean_object* v_cache_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; uint8_t v___x_3379_; 
v___x_3379_ = l_Lean_Expr_hasLooseBVars(v_e_3360_);
if (v___x_3379_ == 0)
{
v___y_3370_ = v_a_3362_;
v___y_3371_ = v_a_3363_;
v___y_3372_ = v_a_3364_;
v___y_3373_ = v_a_3365_;
v___y_3374_ = v_a_3366_;
v___y_3375_ = v_a_3367_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v_cache_3361_);
v___x_3380_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3381_ = l_Lean_indentExpr(v_e_3360_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3382_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
v___jp_3369_:
{
lean_object* v___x_3376_; 
v___x_3376_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3360_, v___y_3370_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3377_, v_cache_3361_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3378_;
}
else
{
lean_dec_ref(v_cache_3361_);
return v___x_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3392_, lean_object* v_cache_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3392_, v_cache_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3402_, lean_object* v_msg_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3403_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3412_, lean_object* v_msg_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3412_, v_msg_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3422_, lean_object* v___x_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3425_, v_e_3422_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3423_);
lean_ctor_set(v___x_3427_, 1, v___y_3425_);
v___x_3428_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3422_, v___y_3424_, v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3438_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 1);
v_a_3430_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3432_ = v___x_3428_;
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3429_);
lean_inc(v_a_3430_);
lean_dec(v___x_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_set_3434_; lean_object* v___x_3436_; 
v_set_3434_ = lean_ctor_get(v_a_3429_, 1);
lean_inc_ref(v_set_3434_);
lean_dec(v_a_3429_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_set_3434_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3430_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_set_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3448_; 
v_a_3439_ = lean_ctor_get(v___x_3428_, 1);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3449_);
v___x_3441_ = v___x_3428_;
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3428_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_map_3443_; lean_object* v_set_3444_; lean_object* v___x_3446_; 
v_map_3443_ = lean_ctor_get(v_a_3439_, 0);
lean_inc_ref(v_map_3443_);
v_set_3444_ = lean_ctor_get(v_a_3439_, 1);
lean_inc_ref(v_set_3444_);
lean_dec(v_a_3439_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v_set_3444_);
lean_ctor_set(v___x_3441_, 0, v_map_3443_);
v___x_3446_ = v___x_3441_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_map_3443_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_set_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_val_3450_; lean_object* v_fst_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v___x_3423_);
lean_dec_ref(v_e_3422_);
v_val_3450_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_val_3450_);
lean_dec_ref_known(v___x_3426_, 1);
v_fst_3451_ = lean_ctor_get(v_val_3450_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_val_3450_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v_val_3450_, 1);
lean_dec(v_unused_3459_);
v___x_3453_ = v_val_3450_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_fst_3451_);
lean_dec(v_val_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___y_3425_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_fst_3451_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___y_3425_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3460_, lean_object* v___x_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3460_, v___x_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___x_3473_; lean_object* v_a_3474_; lean_object* v___x_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3488_; 
v___x_3473_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3466_, v_a_3471_);
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3465_);
v___f_3476_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3476_, 0, v_e_3465_);
lean_closure_set(v___f_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3476_, v_a_3474_, v_a_3467_);
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3488_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3488_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
if (lean_obj_tag(v_a_3478_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; 
lean_del_object(v___x_3480_);
v_a_3482_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v_a_3478_, 1);
v___x_3483_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3465_, v_a_3482_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
return v___x_3483_;
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; 
lean_dec_ref(v_e_3465_);
v_a_3484_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v_a_3478_, 1);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v_a_3484_);
v___x_3486_ = v___x_3480_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Meta_Sym_shareCommon(v_e_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3498_, v___y_3499_, v___y_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3502_, v___y_3503_, v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_){
_start:
{
lean_object* v___x_3514_; lean_object* v_a_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3528_; 
v___x_3514_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3507_, v_a_3512_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref(v___x_3514_);
lean_inc_ref(v_e_3506_);
v___f_3516_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3516_, 0, v_e_3506_);
v___x_3517_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3516_, v_a_3515_, v_a_3508_);
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
if (lean_obj_tag(v_a_3518_) == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref_known(v_a_3518_, 1);
lean_del_object(v___x_3520_);
v___x_3522_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3523_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3506_, v___x_3522_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
return v___x_3523_;
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; 
lean_dec_ref(v_e_3506_);
v_a_3524_ = lean_ctor_get(v_a_3518_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v_a_3518_, 1);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v_a_3524_);
v___x_3526_ = v___x_3520_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_Meta_Sym_share(v_e_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3556_){
_start:
{
lean_object* v___x_3558_; uint8_t v_debug_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3558_ = lean_st_ref_get(v_a_3556_);
v_debug_3559_ = lean_ctor_get_uint8(v___x_3558_, sizeof(void*)*11);
lean_dec(v___x_3558_);
v___x_3560_ = lean_box(v_debug_3559_);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3562_);
lean_dec(v_a_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___x_3572_; uint8_t v_debug_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3572_ = lean_st_ref_get(v_a_3566_);
v_debug_3573_ = lean_ctor_get_uint8(v___x_3572_, sizeof(void*)*11);
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(v_debug_3573_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3584_){
_start:
{
lean_object* v_config_3586_; lean_object* v___x_3587_; 
v_config_3586_ = lean_ctor_get(v_a_3584_, 1);
lean_inc_ref(v_config_3586_);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v_config_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3588_);
lean_dec_ref(v_a_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3591_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Meta_Sym_getConfig(v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3607_, lean_object* v_msg_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_ref_3614_; lean_object* v___x_3615_; lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3660_; 
v_ref_3614_ = lean_ctor_get(v___y_3611_, 5);
v___x_3615_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3660_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3660_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v_traceState_3621_; lean_object* v_env_3622_; lean_object* v_nextMacroScope_3623_; lean_object* v_ngen_3624_; lean_object* v_auxDeclNGen_3625_; lean_object* v_cache_3626_; lean_object* v_messages_3627_; lean_object* v_infoState_3628_; lean_object* v_snapshotTasks_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3659_; 
v___x_3620_ = lean_st_ref_take(v___y_3612_);
v_traceState_3621_ = lean_ctor_get(v___x_3620_, 4);
v_env_3622_ = lean_ctor_get(v___x_3620_, 0);
v_nextMacroScope_3623_ = lean_ctor_get(v___x_3620_, 1);
v_ngen_3624_ = lean_ctor_get(v___x_3620_, 2);
v_auxDeclNGen_3625_ = lean_ctor_get(v___x_3620_, 3);
v_cache_3626_ = lean_ctor_get(v___x_3620_, 5);
v_messages_3627_ = lean_ctor_get(v___x_3620_, 6);
v_infoState_3628_ = lean_ctor_get(v___x_3620_, 7);
v_snapshotTasks_3629_ = lean_ctor_get(v___x_3620_, 8);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3631_ = v___x_3620_;
v_isShared_3632_ = v_isSharedCheck_3659_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_snapshotTasks_3629_);
lean_inc(v_infoState_3628_);
lean_inc(v_messages_3627_);
lean_inc(v_cache_3626_);
lean_inc(v_traceState_3621_);
lean_inc(v_auxDeclNGen_3625_);
lean_inc(v_ngen_3624_);
lean_inc(v_nextMacroScope_3623_);
lean_inc(v_env_3622_);
lean_dec(v___x_3620_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3659_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
uint64_t v_tid_3633_; lean_object* v_traces_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3658_; 
v_tid_3633_ = lean_ctor_get_uint64(v_traceState_3621_, sizeof(void*)*1);
v_traces_3634_ = lean_ctor_get(v_traceState_3621_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_traceState_3621_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3636_ = v_traceState_3621_;
v_isShared_3637_ = v_isSharedCheck_3658_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_traces_3634_);
lean_dec(v_traceState_3621_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3658_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; double v___x_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3638_ = lean_box(0);
v___x_3639_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3640_ = 0;
v___x_3641_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3642_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3642_, 0, v_cls_3607_);
lean_ctor_set(v___x_3642_, 1, v___x_3638_);
lean_ctor_set(v___x_3642_, 2, v___x_3641_);
lean_ctor_set_float(v___x_3642_, sizeof(void*)*3, v___x_3639_);
lean_ctor_set_float(v___x_3642_, sizeof(void*)*3 + 8, v___x_3639_);
lean_ctor_set_uint8(v___x_3642_, sizeof(void*)*3 + 16, v___x_3640_);
v___x_3643_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3644_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v_a_3616_);
lean_ctor_set(v___x_3644_, 2, v___x_3643_);
lean_inc(v_ref_3614_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_ref_3614_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = l_Lean_PersistentArray_push___redArg(v_traces_3634_, v___x_3645_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3646_);
v___x_3648_ = v___x_3636_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3646_);
lean_ctor_set_uint64(v_reuseFailAlloc_3657_, sizeof(void*)*1, v_tid_3633_);
v___x_3648_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 4, v___x_3648_);
v___x_3650_ = v___x_3631_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_env_3622_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_nextMacroScope_3623_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_ngen_3624_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v_auxDeclNGen_3625_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3656_, 5, v_cache_3626_);
lean_ctor_set(v_reuseFailAlloc_3656_, 6, v_messages_3627_);
lean_ctor_set(v_reuseFailAlloc_3656_, 7, v_infoState_3628_);
lean_ctor_set(v_reuseFailAlloc_3656_, 8, v_snapshotTasks_3629_);
v___x_3650_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3651_ = lean_st_ref_set(v___y_3612_, v___x_3650_);
v___x_3652_ = lean_box(0);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3652_);
v___x_3654_ = v___x_3618_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3661_, lean_object* v_msg_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3661_, v_msg_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3668_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3672_; uint8_t v___x_3673_; double v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3672_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3673_ = 1;
v___x_3674_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3675_ = lean_box(0);
v___x_3676_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3677_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
lean_ctor_set(v___x_3677_, 1, v___x_3675_);
lean_ctor_set(v___x_3677_, 2, v___x_3672_);
lean_ctor_set_float(v___x_3677_, sizeof(void*)*3, v___x_3674_);
lean_ctor_set_float(v___x_3677_, sizeof(void*)*3 + 8, v___x_3674_);
lean_ctor_set_uint8(v___x_3677_, sizeof(void*)*3 + 16, v___x_3673_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___x_3689_; lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v_share_3692_; lean_object* v_maxFVar_3693_; lean_object* v_proofInstInfo_3694_; lean_object* v_inferType_3695_; lean_object* v_getLevel_3696_; lean_object* v_congrInfo_3697_; lean_object* v_defEqI_3698_; lean_object* v_extensions_3699_; lean_object* v_issues_3700_; lean_object* v_canon_3701_; lean_object* v_instanceOverrides_3702_; uint8_t v_debug_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3722_; 
v___x_3689_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3678_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref(v___x_3689_);
v___x_3691_ = lean_st_ref_take(v_a_3680_);
v_share_3692_ = lean_ctor_get(v___x_3691_, 0);
v_maxFVar_3693_ = lean_ctor_get(v___x_3691_, 1);
v_proofInstInfo_3694_ = lean_ctor_get(v___x_3691_, 2);
v_inferType_3695_ = lean_ctor_get(v___x_3691_, 3);
v_getLevel_3696_ = lean_ctor_get(v___x_3691_, 4);
v_congrInfo_3697_ = lean_ctor_get(v___x_3691_, 5);
v_defEqI_3698_ = lean_ctor_get(v___x_3691_, 6);
v_extensions_3699_ = lean_ctor_get(v___x_3691_, 7);
v_issues_3700_ = lean_ctor_get(v___x_3691_, 8);
v_canon_3701_ = lean_ctor_get(v___x_3691_, 9);
v_instanceOverrides_3702_ = lean_ctor_get(v___x_3691_, 10);
v_debug_3703_ = lean_ctor_get_uint8(v___x_3691_, sizeof(void*)*11);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3705_ = v___x_3691_;
v_isShared_3706_ = v_isSharedCheck_3722_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_instanceOverrides_3702_);
lean_inc(v_canon_3701_);
lean_inc(v_issues_3700_);
lean_inc(v_extensions_3699_);
lean_inc(v_defEqI_3698_);
lean_inc(v_congrInfo_3697_);
lean_inc(v_getLevel_3696_);
lean_inc(v_inferType_3695_);
lean_inc(v_proofInstInfo_3694_);
lean_inc(v_maxFVar_3693_);
lean_inc(v_share_3692_);
lean_dec(v___x_3691_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3722_;
goto v_resetjp_3704_;
}
v___jp_3686_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = lean_box(0);
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
v___x_3707_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3708_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3690_);
v___x_3709_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v_a_3690_);
lean_ctor_set(v___x_3709_, 2, v___x_3708_);
v___x_3710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v_issues_3700_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 8, v___x_3710_);
v___x_3712_ = v___x_3705_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_share_3692_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_maxFVar_3693_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_proofInstInfo_3694_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_inferType_3695_);
lean_ctor_set(v_reuseFailAlloc_3721_, 4, v_getLevel_3696_);
lean_ctor_set(v_reuseFailAlloc_3721_, 5, v_congrInfo_3697_);
lean_ctor_set(v_reuseFailAlloc_3721_, 6, v_defEqI_3698_);
lean_ctor_set(v_reuseFailAlloc_3721_, 7, v_extensions_3699_);
lean_ctor_set(v_reuseFailAlloc_3721_, 8, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3721_, 9, v_canon_3701_);
lean_ctor_set(v_reuseFailAlloc_3721_, 10, v_instanceOverrides_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3721_, sizeof(void*)*11, v_debug_3703_);
v___x_3712_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v_options_3714_; uint8_t v_hasTrace_3715_; 
v___x_3713_ = lean_st_ref_set(v_a_3680_, v___x_3712_);
v_options_3714_ = lean_ctor_get(v_a_3683_, 2);
v_hasTrace_3715_ = lean_ctor_get_uint8(v_options_3714_, sizeof(void*)*1);
if (v_hasTrace_3715_ == 0)
{
lean_dec(v_a_3690_);
goto v___jp_3686_;
}
else
{
lean_object* v_inheritedTraceOptions_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_inheritedTraceOptions_3716_ = lean_ctor_get(v_a_3683_, 13);
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3718_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3716_, v_options_3714_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_dec(v_a_3690_);
goto v___jp_3686_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3717_, v_a_3690_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
return v___x_3720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Meta_Sym_reportIssue(v_msg_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3732_, lean_object* v_msg_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3732_, v_msg_3733_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3742_, lean_object* v_msg_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3742_, v_msg_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v___x_3760_; lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3771_; 
v___x_3760_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3753_);
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3771_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3771_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
uint8_t v_verbose_3765_; 
v_verbose_3765_ = lean_ctor_get_uint8(v_a_3761_, 0);
lean_dec(v_a_3761_);
if (v_verbose_3765_ == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec_ref(v_msg_3752_);
v___x_3766_ = lean_box(0);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3766_);
v___x_3768_ = v___x_3763_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
else
{
lean_object* v___x_3770_; 
lean_del_object(v___x_3763_);
v___x_3770_ = l_Lean_Meta_Sym_reportIssue(v_msg_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
return v___x_3770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
return v_res_3780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3797_ = l_String_toRawSubstring_x27(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3836_ = l_String_toRawSubstring_x27(v___x_3835_);
return v___x_3836_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3849_ = l_String_toRawSubstring_x27(v___x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_msg_3876_; lean_object* v_quotContext_3877_; lean_object* v_currMacroScope_3878_; lean_object* v_ref_3879_; lean_object* v___y_3880_; lean_object* v___x_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
lean_inc(v_s_3872_);
v___x_3895_ = l_Lean_Syntax_getKind(v_s_3872_);
v___x_3896_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3897_ = lean_name_eq(v___x_3895_, v___x_3896_);
lean_dec(v___x_3895_);
if (v___x_3897_ == 0)
{
lean_object* v_quotContext_3898_; lean_object* v_currMacroScope_3899_; lean_object* v_ref_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_quotContext_3898_ = lean_ctor_get(v_a_3873_, 1);
v_currMacroScope_3899_ = lean_ctor_get(v_a_3873_, 2);
v_ref_3900_ = lean_ctor_get(v_a_3873_, 5);
v___x_3901_ = l_Lean_SourceInfo_fromRef(v_ref_3900_, v___x_3897_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3903_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3904_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3901_, 8);
v___x_3905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3901_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
v___x_3906_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3907_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3908_ = lean_box(0);
lean_inc_n(v_currMacroScope_3899_, 3);
lean_inc_n(v_quotContext_3898_, 3);
v___x_3909_ = l_Lean_addMacroScope(v_quotContext_3898_, v___x_3908_, v_currMacroScope_3899_);
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3901_);
lean_ctor_set(v___x_3911_, 1, v___x_3907_);
lean_ctor_set(v___x_3911_, 2, v___x_3909_);
lean_ctor_set(v___x_3911_, 3, v___x_3910_);
v___x_3912_ = l_Lean_Syntax_node1(v___x_3901_, v___x_3906_, v___x_3911_);
v___x_3913_ = l_Lean_Syntax_node2(v___x_3901_, v___x_3903_, v___x_3905_, v___x_3912_);
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_3915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3901_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3917_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_3919_ = l_Lean_addMacroScope(v_quotContext_3898_, v___x_3918_, v_currMacroScope_3899_);
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_3921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3901_);
lean_ctor_set(v___x_3921_, 1, v___x_3917_);
lean_ctor_set(v___x_3921_, 2, v___x_3919_);
lean_ctor_set(v___x_3921_, 3, v___x_3920_);
v___x_3922_ = l_Lean_Syntax_node1(v___x_3901_, v___x_3916_, v___x_3921_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_3924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3901_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = l_Lean_Syntax_node5(v___x_3901_, v___x_3902_, v___x_3913_, v_s_3872_, v___x_3915_, v___x_3922_, v___x_3924_);
v_msg_3876_ = v___x_3925_;
v_quotContext_3877_ = v_quotContext_3898_;
v_currMacroScope_3878_ = v_currMacroScope_3899_;
v_ref_3879_ = v_ref_3900_;
v___y_3880_ = v_a_3874_;
goto v___jp_3875_;
}
else
{
lean_object* v_quotContext_3926_; lean_object* v_currMacroScope_3927_; lean_object* v_ref_3928_; uint8_t v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_quotContext_3926_ = lean_ctor_get(v_a_3873_, 1);
v_currMacroScope_3927_ = lean_ctor_get(v_a_3873_, 2);
v_ref_3928_ = lean_ctor_get(v_a_3873_, 5);
v___x_3929_ = 0;
v___x_3930_ = l_Lean_SourceInfo_fromRef(v_ref_3928_, v___x_3929_);
v___x_3931_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_3932_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_3930_);
v___x_3933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3930_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = l_Lean_Syntax_node2(v___x_3930_, v___x_3931_, v___x_3933_, v_s_3872_);
lean_inc(v_currMacroScope_3927_);
lean_inc(v_quotContext_3926_);
v_msg_3876_ = v___x_3934_;
v_quotContext_3877_ = v_quotContext_3926_;
v_currMacroScope_3878_ = v_currMacroScope_3927_;
v_ref_3879_ = v_ref_3928_;
v___y_3880_ = v_a_3874_;
goto v___jp_3875_;
}
v___jp_3875_:
{
uint8_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3881_ = 0;
v___x_3882_ = l_Lean_SourceInfo_fromRef(v_ref_3879_, v___x_3881_);
v___x_3883_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3884_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3885_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3886_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3887_ = l_Lean_addMacroScope(v_quotContext_3877_, v___x_3886_, v_currMacroScope_3878_);
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3882_, 3);
v___x_3889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3882_);
lean_ctor_set(v___x_3889_, 1, v___x_3885_);
lean_ctor_set(v___x_3889_, 2, v___x_3887_);
lean_ctor_set(v___x_3889_, 3, v___x_3888_);
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3891_ = l_Lean_Syntax_node1(v___x_3882_, v___x_3890_, v_msg_3876_);
v___x_3892_ = l_Lean_Syntax_node2(v___x_3882_, v___x_3884_, v___x_3889_, v___x_3891_);
v___x_3893_ = l_Lean_Syntax_node1(v___x_3882_, v___x_3883_, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v___y_3880_);
return v___x_3894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_3935_, v_a_3936_, v_a_3937_);
lean_dec_ref(v_a_3936_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_3979_);
v___x_3983_ = l_Lean_Syntax_isOfKind(v_x_3979_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_dec(v_x_3979_);
v___x_3984_ = lean_box(1);
v___x_3985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v_a_3981_);
return v___x_3985_;
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_a_3989_; lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = l_Lean_Syntax_getArg(v_x_3979_, v___x_3986_);
lean_dec(v_x_3979_);
v___x_3988_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_3987_, v_a_3980_, v_a_3981_);
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
v_a_3990_ = lean_ctor_get(v___x_3988_, 1);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3988_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_inc(v_a_3989_);
lean_dec(v___x_3988_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3989_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_3998_, v_a_3999_, v_a_4000_);
lean_dec_ref(v_a_3999_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4010_; lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4030_; 
v___x_4010_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4003_);
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4030_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4030_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
uint8_t v_verbose_4015_; 
v_verbose_4015_ = lean_ctor_get_uint8(v_a_4011_, 0);
lean_dec(v_a_4011_);
if (v_verbose_4015_ == 0)
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
lean_dec_ref(v_msg_4002_);
v___x_4016_ = lean_box(0);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4016_);
v___x_4018_ = v___x_4013_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
else
{
lean_object* v_options_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; 
v_options_4020_ = lean_ctor_get(v_a_4007_, 2);
v___x_4021_ = l_Lean_KVMap_instValueBool;
v___x_4022_ = l_Lean_Meta_Sym_sym_debug;
v___x_4023_ = l_Lean_Option_get___redArg(v___x_4021_, v_options_4020_, v___x_4022_);
v___x_4024_ = lean_unbox(v___x_4023_);
lean_dec(v___x_4023_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_dec_ref(v_msg_4002_);
v___x_4025_ = lean_box(0);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4025_);
v___x_4027_ = v___x_4013_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
else
{
lean_object* v___x_4029_; 
lean_del_object(v___x_4013_);
v___x_4029_ = l_Lean_Meta_Sym_reportIssue(v_msg_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
return v___x_4029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
return v_res_4039_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4042_ = l_String_toRawSubstring_x27(v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_msg_4062_; lean_object* v_quotContext_4063_; lean_object* v_currMacroScope_4064_; lean_object* v_ref_4065_; lean_object* v___y_4066_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
lean_inc(v_s_4058_);
v___x_4081_ = l_Lean_Syntax_getKind(v_s_4058_);
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4083_ = lean_name_eq(v___x_4081_, v___x_4082_);
lean_dec(v___x_4081_);
if (v___x_4083_ == 0)
{
lean_object* v_quotContext_4084_; lean_object* v_currMacroScope_4085_; lean_object* v_ref_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_quotContext_4084_ = lean_ctor_get(v_a_4059_, 1);
v_currMacroScope_4085_ = lean_ctor_get(v_a_4059_, 2);
v_ref_4086_ = lean_ctor_get(v_a_4059_, 5);
v___x_4087_ = l_Lean_SourceInfo_fromRef(v_ref_4086_, v___x_4083_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4087_, 8);
v___x_4091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4087_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4093_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4094_ = lean_box(0);
lean_inc_n(v_currMacroScope_4085_, 3);
lean_inc_n(v_quotContext_4084_, 3);
v___x_4095_ = l_Lean_addMacroScope(v_quotContext_4084_, v___x_4094_, v_currMacroScope_4085_);
v___x_4096_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4087_);
lean_ctor_set(v___x_4097_, 1, v___x_4093_);
lean_ctor_set(v___x_4097_, 2, v___x_4095_);
lean_ctor_set(v___x_4097_, 3, v___x_4096_);
v___x_4098_ = l_Lean_Syntax_node1(v___x_4087_, v___x_4092_, v___x_4097_);
v___x_4099_ = l_Lean_Syntax_node2(v___x_4087_, v___x_4089_, v___x_4091_, v___x_4098_);
v___x_4100_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4087_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4103_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4105_ = l_Lean_addMacroScope(v_quotContext_4084_, v___x_4104_, v_currMacroScope_4085_);
v___x_4106_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4107_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4087_);
lean_ctor_set(v___x_4107_, 1, v___x_4103_);
lean_ctor_set(v___x_4107_, 2, v___x_4105_);
lean_ctor_set(v___x_4107_, 3, v___x_4106_);
v___x_4108_ = l_Lean_Syntax_node1(v___x_4087_, v___x_4102_, v___x_4107_);
v___x_4109_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4087_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node5(v___x_4087_, v___x_4088_, v___x_4099_, v_s_4058_, v___x_4101_, v___x_4108_, v___x_4110_);
v_msg_4062_ = v___x_4111_;
v_quotContext_4063_ = v_quotContext_4084_;
v_currMacroScope_4064_ = v_currMacroScope_4085_;
v_ref_4065_ = v_ref_4086_;
v___y_4066_ = v_a_4060_;
goto v___jp_4061_;
}
else
{
lean_object* v_quotContext_4112_; lean_object* v_currMacroScope_4113_; lean_object* v_ref_4114_; uint8_t v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_quotContext_4112_ = lean_ctor_get(v_a_4059_, 1);
v_currMacroScope_4113_ = lean_ctor_get(v_a_4059_, 2);
v_ref_4114_ = lean_ctor_get(v_a_4059_, 5);
v___x_4115_ = 0;
v___x_4116_ = l_Lean_SourceInfo_fromRef(v_ref_4114_, v___x_4115_);
v___x_4117_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4118_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4116_);
v___x_4119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4116_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = l_Lean_Syntax_node2(v___x_4116_, v___x_4117_, v___x_4119_, v_s_4058_);
lean_inc(v_currMacroScope_4113_);
lean_inc(v_quotContext_4112_);
v_msg_4062_ = v___x_4120_;
v_quotContext_4063_ = v_quotContext_4112_;
v_currMacroScope_4064_ = v_currMacroScope_4113_;
v_ref_4065_ = v_ref_4114_;
v___y_4066_ = v_a_4060_;
goto v___jp_4061_;
}
v___jp_4061_:
{
uint8_t v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4067_ = 0;
v___x_4068_ = l_Lean_SourceInfo_fromRef(v_ref_4065_, v___x_4067_);
v___x_4069_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4070_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4071_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4072_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4073_ = l_Lean_addMacroScope(v_quotContext_4063_, v___x_4072_, v_currMacroScope_4064_);
v___x_4074_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4068_, 3);
v___x_4075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4068_);
lean_ctor_set(v___x_4075_, 1, v___x_4071_);
lean_ctor_set(v___x_4075_, 2, v___x_4073_);
lean_ctor_set(v___x_4075_, 3, v___x_4074_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4077_ = l_Lean_Syntax_node1(v___x_4068_, v___x_4076_, v_msg_4062_);
v___x_4078_ = l_Lean_Syntax_node2(v___x_4068_, v___x_4070_, v___x_4075_, v___x_4077_);
v___x_4079_ = l_Lean_Syntax_node1(v___x_4068_, v___x_4069_, v___x_4078_);
v___x_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___y_4066_);
return v___x_4080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4121_, v_a_4122_, v_a_4123_);
lean_dec_ref(v_a_4122_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4146_; uint8_t v___x_4147_; 
v___x_4146_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4143_);
v___x_4147_ = l_Lean_Syntax_isOfKind(v_x_4143_, v___x_4146_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_dec(v_x_4143_);
v___x_4148_ = lean_box(1);
v___x_4149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
lean_ctor_set(v___x_4149_, 1, v_a_4145_);
return v___x_4149_;
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v_a_4153_; lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
v___x_4150_ = lean_unsigned_to_nat(1u);
v___x_4151_ = l_Lean_Syntax_getArg(v_x_4143_, v___x_4150_);
lean_dec(v_x_4143_);
v___x_4152_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4151_, v_a_4144_, v_a_4145_);
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_a_4154_ = lean_ctor_get(v___x_4152_, 1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4152_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4153_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4162_, v_a_4163_, v_a_4164_);
lean_dec_ref(v_a_4163_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4166_){
_start:
{
lean_object* v___x_4168_; lean_object* v_issues_4169_; lean_object* v___x_4170_; 
v___x_4168_ = lean_st_ref_get(v_a_4166_);
v_issues_4169_ = lean_ctor_get(v___x_4168_, 8);
lean_inc(v_issues_4169_);
lean_dec(v___x_4168_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v_issues_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4171_);
lean_dec(v_a_4171_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4175_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_Meta_Sym_getIssues(v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4190_, lean_object* v_issues_4191_, lean_object* v_a_x3f_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v_share_4195_; lean_object* v_maxFVar_4196_; lean_object* v_proofInstInfo_4197_; lean_object* v_inferType_4198_; lean_object* v_getLevel_4199_; lean_object* v_congrInfo_4200_; lean_object* v_defEqI_4201_; lean_object* v_extensions_4202_; lean_object* v_issues_4203_; lean_object* v_canon_4204_; lean_object* v_instanceOverrides_4205_; uint8_t v_debug_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4217_; 
v___x_4194_ = lean_st_ref_take(v_a_4190_);
v_share_4195_ = lean_ctor_get(v___x_4194_, 0);
v_maxFVar_4196_ = lean_ctor_get(v___x_4194_, 1);
v_proofInstInfo_4197_ = lean_ctor_get(v___x_4194_, 2);
v_inferType_4198_ = lean_ctor_get(v___x_4194_, 3);
v_getLevel_4199_ = lean_ctor_get(v___x_4194_, 4);
v_congrInfo_4200_ = lean_ctor_get(v___x_4194_, 5);
v_defEqI_4201_ = lean_ctor_get(v___x_4194_, 6);
v_extensions_4202_ = lean_ctor_get(v___x_4194_, 7);
v_issues_4203_ = lean_ctor_get(v___x_4194_, 8);
v_canon_4204_ = lean_ctor_get(v___x_4194_, 9);
v_instanceOverrides_4205_ = lean_ctor_get(v___x_4194_, 10);
v_debug_4206_ = lean_ctor_get_uint8(v___x_4194_, sizeof(void*)*11);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4208_ = v___x_4194_;
v_isShared_4209_ = v_isSharedCheck_4217_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_instanceOverrides_4205_);
lean_inc(v_canon_4204_);
lean_inc(v_issues_4203_);
lean_inc(v_extensions_4202_);
lean_inc(v_defEqI_4201_);
lean_inc(v_congrInfo_4200_);
lean_inc(v_getLevel_4199_);
lean_inc(v_inferType_4198_);
lean_inc(v_proofInstInfo_4197_);
lean_inc(v_maxFVar_4196_);
lean_inc(v_share_4195_);
lean_dec(v___x_4194_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4217_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = l_List_appendTR___redArg(v_issues_4203_, v_issues_4191_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 8, v___x_4210_);
v___x_4212_ = v___x_4208_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_share_4195_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_maxFVar_4196_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_proofInstInfo_4197_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v_inferType_4198_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v_getLevel_4199_);
lean_ctor_set(v_reuseFailAlloc_4216_, 5, v_congrInfo_4200_);
lean_ctor_set(v_reuseFailAlloc_4216_, 6, v_defEqI_4201_);
lean_ctor_set(v_reuseFailAlloc_4216_, 7, v_extensions_4202_);
lean_ctor_set(v_reuseFailAlloc_4216_, 8, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4216_, 9, v_canon_4204_);
lean_ctor_set(v_reuseFailAlloc_4216_, 10, v_instanceOverrides_4205_);
lean_ctor_set_uint8(v_reuseFailAlloc_4216_, sizeof(void*)*11, v_debug_4206_);
v___x_4212_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = lean_st_ref_set(v_a_4190_, v___x_4212_);
v___x_4214_ = lean_box(0);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4218_, lean_object* v_issues_4219_, lean_object* v_a_x3f_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4218_, v_issues_4219_, v_a_x3f_4220_);
lean_dec(v_a_x3f_4220_);
lean_dec(v_a_4218_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_share_4233_; lean_object* v_maxFVar_4234_; lean_object* v_proofInstInfo_4235_; lean_object* v_inferType_4236_; lean_object* v_getLevel_4237_; lean_object* v_congrInfo_4238_; lean_object* v_defEqI_4239_; lean_object* v_extensions_4240_; lean_object* v_canon_4241_; lean_object* v_instanceOverrides_4242_; uint8_t v_debug_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4282_; 
v___x_4231_ = lean_st_ref_get(v_a_4225_);
v___x_4232_ = lean_st_ref_take(v_a_4225_);
v_share_4233_ = lean_ctor_get(v___x_4232_, 0);
v_maxFVar_4234_ = lean_ctor_get(v___x_4232_, 1);
v_proofInstInfo_4235_ = lean_ctor_get(v___x_4232_, 2);
v_inferType_4236_ = lean_ctor_get(v___x_4232_, 3);
v_getLevel_4237_ = lean_ctor_get(v___x_4232_, 4);
v_congrInfo_4238_ = lean_ctor_get(v___x_4232_, 5);
v_defEqI_4239_ = lean_ctor_get(v___x_4232_, 6);
v_extensions_4240_ = lean_ctor_get(v___x_4232_, 7);
v_canon_4241_ = lean_ctor_get(v___x_4232_, 9);
v_instanceOverrides_4242_ = lean_ctor_get(v___x_4232_, 10);
v_debug_4243_ = lean_ctor_get_uint8(v___x_4232_, sizeof(void*)*11);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; 
v_unused_4283_ = lean_ctor_get(v___x_4232_, 8);
lean_dec(v_unused_4283_);
v___x_4245_ = v___x_4232_;
v_isShared_4246_ = v_isSharedCheck_4282_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_instanceOverrides_4242_);
lean_inc(v_canon_4241_);
lean_inc(v_extensions_4240_);
lean_inc(v_defEqI_4239_);
lean_inc(v_congrInfo_4238_);
lean_inc(v_getLevel_4237_);
lean_inc(v_inferType_4236_);
lean_inc(v_proofInstInfo_4235_);
lean_inc(v_maxFVar_4234_);
lean_inc(v_share_4233_);
lean_dec(v___x_4232_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4282_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4247_ = lean_box(0);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 8, v___x_4247_);
v___x_4249_ = v___x_4245_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_share_4233_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_maxFVar_4234_);
lean_ctor_set(v_reuseFailAlloc_4281_, 2, v_proofInstInfo_4235_);
lean_ctor_set(v_reuseFailAlloc_4281_, 3, v_inferType_4236_);
lean_ctor_set(v_reuseFailAlloc_4281_, 4, v_getLevel_4237_);
lean_ctor_set(v_reuseFailAlloc_4281_, 5, v_congrInfo_4238_);
lean_ctor_set(v_reuseFailAlloc_4281_, 6, v_defEqI_4239_);
lean_ctor_set(v_reuseFailAlloc_4281_, 7, v_extensions_4240_);
lean_ctor_set(v_reuseFailAlloc_4281_, 8, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4281_, 9, v_canon_4241_);
lean_ctor_set(v_reuseFailAlloc_4281_, 10, v_instanceOverrides_4242_);
lean_ctor_set_uint8(v_reuseFailAlloc_4281_, sizeof(void*)*11, v_debug_4243_);
v___x_4249_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; lean_object* v_issues_4251_; lean_object* v_r_4252_; 
v___x_4250_ = lean_st_ref_set(v_a_4225_, v___x_4249_);
v_issues_4251_ = lean_ctor_get(v___x_4231_, 8);
lean_inc(v_issues_4251_);
lean_dec(v___x_4231_);
lean_inc(v_a_4229_);
lean_inc_ref(v_a_4228_);
lean_inc(v_a_4227_);
lean_inc_ref(v_a_4226_);
lean_inc(v_a_4225_);
lean_inc_ref(v_a_4224_);
v_r_4252_ = lean_apply_7(v_x_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, lean_box(0));
if (lean_obj_tag(v_r_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4269_; 
v_a_4253_ = lean_ctor_get(v_r_4252_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v_r_4252_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4255_ = v_r_4252_;
v_isShared_4256_ = v_isSharedCheck_4269_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v_r_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4269_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
lean_inc(v_a_4253_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set_tag(v___x_4255_, 1);
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
v___x_4259_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4225_, v_issues_4251_, v___x_4258_);
lean_dec_ref(v___x_4258_);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4266_ == 0)
{
lean_object* v_unused_4267_; 
v_unused_4267_ = lean_ctor_get(v___x_4259_, 0);
lean_dec(v_unused_4267_);
v___x_4261_ = v___x_4259_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_dec(v___x_4259_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v_a_4253_);
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4253_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_a_4270_ = lean_ctor_get(v_r_4252_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v_r_4252_, 1);
v___x_4271_ = lean_box(0);
v___x_4272_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4225_, v_issues_4251_, v___x_4271_);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; 
v_unused_4280_ = lean_ctor_get(v___x_4272_, 0);
lean_dec(v_unused_4280_);
v___x_4274_ = v___x_4272_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v___x_4272_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
lean_ctor_set_tag(v___x_4274_, 1);
lean_ctor_set(v___x_4274_, 0, v_a_4270_);
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4270_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4293_, lean_object* v_x_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4303_, lean_object* v_x_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4303_, v_x_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4313_, lean_object* v_vals_4314_, lean_object* v_i_4315_, lean_object* v_k_4316_){
_start:
{
uint8_t v___y_4318_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = lean_array_get_size(v_keys_4313_);
v___x_4325_ = lean_nat_dec_lt(v_i_4315_, v___x_4324_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; 
lean_dec(v_i_4315_);
v___x_4326_ = lean_box(0);
return v___x_4326_;
}
else
{
lean_object* v_fst_4327_; lean_object* v_snd_4328_; lean_object* v_k_x27_4329_; lean_object* v_fst_4330_; lean_object* v_snd_4331_; size_t v___x_4332_; size_t v___x_4333_; uint8_t v___x_4334_; 
v_fst_4327_ = lean_ctor_get(v_k_4316_, 0);
v_snd_4328_ = lean_ctor_get(v_k_4316_, 1);
v_k_x27_4329_ = lean_array_fget_borrowed(v_keys_4313_, v_i_4315_);
v_fst_4330_ = lean_ctor_get(v_k_x27_4329_, 0);
v_snd_4331_ = lean_ctor_get(v_k_x27_4329_, 1);
v___x_4332_ = lean_ptr_addr(v_fst_4327_);
v___x_4333_ = lean_ptr_addr(v_fst_4330_);
v___x_4334_ = lean_usize_dec_eq(v___x_4332_, v___x_4333_);
if (v___x_4334_ == 0)
{
v___y_4318_ = v___x_4334_;
goto v___jp_4317_;
}
else
{
size_t v___x_4335_; size_t v___x_4336_; uint8_t v___x_4337_; 
v___x_4335_ = lean_ptr_addr(v_snd_4328_);
v___x_4336_ = lean_ptr_addr(v_snd_4331_);
v___x_4337_ = lean_usize_dec_eq(v___x_4335_, v___x_4336_);
v___y_4318_ = v___x_4337_;
goto v___jp_4317_;
}
}
v___jp_4317_:
{
if (v___y_4318_ == 0)
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_unsigned_to_nat(1u);
v___x_4320_ = lean_nat_add(v_i_4315_, v___x_4319_);
lean_dec(v_i_4315_);
v_i_4315_ = v___x_4320_;
goto _start;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = lean_array_fget_borrowed(v_vals_4314_, v_i_4315_);
lean_dec(v_i_4315_);
lean_inc(v___x_4322_);
v___x_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
return v___x_4323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4338_, lean_object* v_vals_4339_, lean_object* v_i_4340_, lean_object* v_k_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4338_, v_vals_4339_, v_i_4340_, v_k_4341_);
lean_dec_ref(v_k_4341_);
lean_dec_ref(v_vals_4339_);
lean_dec_ref(v_keys_4338_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4343_, size_t v_x_4344_, lean_object* v_x_4345_){
_start:
{
if (lean_obj_tag(v_x_4343_) == 0)
{
lean_object* v_es_4346_; lean_object* v___x_4347_; size_t v___x_4348_; size_t v___x_4349_; lean_object* v_j_4350_; lean_object* v___x_4351_; 
v_es_4346_ = lean_ctor_get(v_x_4343_, 0);
v___x_4347_ = lean_box(2);
v___x_4348_ = ((size_t)31ULL);
v___x_4349_ = lean_usize_land(v_x_4344_, v___x_4348_);
v_j_4350_ = lean_usize_to_nat(v___x_4349_);
v___x_4351_ = lean_array_get_borrowed(v___x_4347_, v_es_4346_, v_j_4350_);
lean_dec(v_j_4350_);
switch(lean_obj_tag(v___x_4351_))
{
case 0:
{
lean_object* v_key_4352_; lean_object* v_val_4353_; uint8_t v___y_4355_; lean_object* v_fst_4358_; lean_object* v_snd_4359_; lean_object* v_fst_4360_; lean_object* v_snd_4361_; size_t v___x_4362_; size_t v___x_4363_; uint8_t v___x_4364_; 
v_key_4352_ = lean_ctor_get(v___x_4351_, 0);
v_val_4353_ = lean_ctor_get(v___x_4351_, 1);
v_fst_4358_ = lean_ctor_get(v_x_4345_, 0);
v_snd_4359_ = lean_ctor_get(v_x_4345_, 1);
v_fst_4360_ = lean_ctor_get(v_key_4352_, 0);
v_snd_4361_ = lean_ctor_get(v_key_4352_, 1);
v___x_4362_ = lean_ptr_addr(v_fst_4358_);
v___x_4363_ = lean_ptr_addr(v_fst_4360_);
v___x_4364_ = lean_usize_dec_eq(v___x_4362_, v___x_4363_);
if (v___x_4364_ == 0)
{
v___y_4355_ = v___x_4364_;
goto v___jp_4354_;
}
else
{
size_t v___x_4365_; size_t v___x_4366_; uint8_t v___x_4367_; 
v___x_4365_ = lean_ptr_addr(v_snd_4359_);
v___x_4366_ = lean_ptr_addr(v_snd_4361_);
v___x_4367_ = lean_usize_dec_eq(v___x_4365_, v___x_4366_);
v___y_4355_ = v___x_4367_;
goto v___jp_4354_;
}
v___jp_4354_:
{
if (v___y_4355_ == 0)
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_box(0);
return v___x_4356_;
}
else
{
lean_object* v___x_4357_; 
lean_inc(v_val_4353_);
v___x_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4357_, 0, v_val_4353_);
return v___x_4357_;
}
}
}
case 1:
{
lean_object* v_node_4368_; size_t v___x_4369_; size_t v___x_4370_; 
v_node_4368_ = lean_ctor_get(v___x_4351_, 0);
v___x_4369_ = ((size_t)5ULL);
v___x_4370_ = lean_usize_shift_right(v_x_4344_, v___x_4369_);
v_x_4343_ = v_node_4368_;
v_x_4344_ = v___x_4370_;
goto _start;
}
default: 
{
lean_object* v___x_4372_; 
v___x_4372_ = lean_box(0);
return v___x_4372_;
}
}
}
else
{
lean_object* v_ks_4373_; lean_object* v_vs_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_ks_4373_ = lean_ctor_get(v_x_4343_, 0);
v_vs_4374_ = lean_ctor_get(v_x_4343_, 1);
v___x_4375_ = lean_unsigned_to_nat(0u);
v___x_4376_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4373_, v_vs_4374_, v___x_4375_, v_x_4345_);
return v___x_4376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4377_, lean_object* v_x_4378_, lean_object* v_x_4379_){
_start:
{
size_t v_x_2767__boxed_4380_; lean_object* v_res_4381_; 
v_x_2767__boxed_4380_ = lean_unbox_usize(v_x_4378_);
lean_dec(v_x_4378_);
v_res_4381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4377_, v_x_2767__boxed_4380_, v_x_4379_);
lean_dec_ref(v_x_4379_);
lean_dec_ref(v_x_4377_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4382_, lean_object* v_x_4383_){
_start:
{
lean_object* v_fst_4384_; lean_object* v_snd_4385_; size_t v___x_4386_; size_t v___x_4387_; size_t v___x_4388_; uint64_t v___x_4389_; size_t v___x_4390_; size_t v___x_4391_; uint64_t v___x_4392_; uint64_t v___x_4393_; size_t v___x_4394_; lean_object* v___x_4395_; 
v_fst_4384_ = lean_ctor_get(v_x_4383_, 0);
v_snd_4385_ = lean_ctor_get(v_x_4383_, 1);
v___x_4386_ = lean_ptr_addr(v_fst_4384_);
v___x_4387_ = ((size_t)3ULL);
v___x_4388_ = lean_usize_shift_right(v___x_4386_, v___x_4387_);
v___x_4389_ = lean_usize_to_uint64(v___x_4388_);
v___x_4390_ = lean_ptr_addr(v_snd_4385_);
v___x_4391_ = lean_usize_shift_right(v___x_4390_, v___x_4387_);
v___x_4392_ = lean_usize_to_uint64(v___x_4391_);
v___x_4393_ = lean_uint64_mix_hash(v___x_4389_, v___x_4392_);
v___x_4394_ = lean_uint64_to_usize(v___x_4393_);
v___x_4395_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4382_, v___x_4394_, v_x_4383_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4396_, lean_object* v_x_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4396_, v_x_4397_);
lean_dec_ref(v_x_4397_);
lean_dec_ref(v_x_4396_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4399_, lean_object* v_x_4400_, lean_object* v_x_4401_, lean_object* v_x_4402_){
_start:
{
lean_object* v_ks_4403_; lean_object* v_vs_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4437_; 
v_ks_4403_ = lean_ctor_get(v_x_4399_, 0);
v_vs_4404_ = lean_ctor_get(v_x_4399_, 1);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_x_4399_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4406_ = v_x_4399_;
v_isShared_4407_ = v_isSharedCheck_4437_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_vs_4404_);
lean_inc(v_ks_4403_);
lean_dec(v_x_4399_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4437_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
uint8_t v___y_4409_; lean_object* v___x_4421_; uint8_t v___x_4422_; 
v___x_4421_ = lean_array_get_size(v_ks_4403_);
v___x_4422_ = lean_nat_dec_lt(v_x_4400_, v___x_4421_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_del_object(v___x_4406_);
lean_dec(v_x_4400_);
v___x_4423_ = lean_array_push(v_ks_4403_, v_x_4401_);
v___x_4424_ = lean_array_push(v_vs_4404_, v_x_4402_);
v___x_4425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
return v___x_4425_;
}
else
{
lean_object* v_fst_4426_; lean_object* v_snd_4427_; lean_object* v_k_x27_4428_; lean_object* v_fst_4429_; lean_object* v_snd_4430_; size_t v___x_4431_; size_t v___x_4432_; uint8_t v___x_4433_; 
v_fst_4426_ = lean_ctor_get(v_x_4401_, 0);
v_snd_4427_ = lean_ctor_get(v_x_4401_, 1);
v_k_x27_4428_ = lean_array_fget_borrowed(v_ks_4403_, v_x_4400_);
v_fst_4429_ = lean_ctor_get(v_k_x27_4428_, 0);
v_snd_4430_ = lean_ctor_get(v_k_x27_4428_, 1);
v___x_4431_ = lean_ptr_addr(v_fst_4426_);
v___x_4432_ = lean_ptr_addr(v_fst_4429_);
v___x_4433_ = lean_usize_dec_eq(v___x_4431_, v___x_4432_);
if (v___x_4433_ == 0)
{
v___y_4409_ = v___x_4433_;
goto v___jp_4408_;
}
else
{
size_t v___x_4434_; size_t v___x_4435_; uint8_t v___x_4436_; 
v___x_4434_ = lean_ptr_addr(v_snd_4427_);
v___x_4435_ = lean_ptr_addr(v_snd_4430_);
v___x_4436_ = lean_usize_dec_eq(v___x_4434_, v___x_4435_);
v___y_4409_ = v___x_4436_;
goto v___jp_4408_;
}
}
v___jp_4408_:
{
if (v___y_4409_ == 0)
{
lean_object* v___x_4411_; 
if (v_isShared_4407_ == 0)
{
v___x_4411_ = v___x_4406_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_ks_4403_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_vs_4404_);
v___x_4411_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_unsigned_to_nat(1u);
v___x_4413_ = lean_nat_add(v_x_4400_, v___x_4412_);
lean_dec(v_x_4400_);
v_x_4399_ = v___x_4411_;
v_x_4400_ = v___x_4413_;
goto _start;
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4416_ = lean_array_fset(v_ks_4403_, v_x_4400_, v_x_4401_);
v___x_4417_ = lean_array_fset(v_vs_4404_, v_x_4400_, v_x_4402_);
lean_dec(v_x_4400_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 1, v___x_4417_);
lean_ctor_set(v___x_4406_, 0, v___x_4416_);
v___x_4419_ = v___x_4406_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4438_, lean_object* v_k_4439_, lean_object* v_v_4440_){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = lean_unsigned_to_nat(0u);
v___x_4442_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4438_, v___x_4441_, v_k_4439_, v_v_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4444_, size_t v_x_4445_, size_t v_x_4446_, lean_object* v_x_4447_, lean_object* v_x_4448_){
_start:
{
if (lean_obj_tag(v_x_4444_) == 0)
{
lean_object* v_es_4449_; size_t v___x_4450_; size_t v___x_4451_; lean_object* v_j_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; 
v_es_4449_ = lean_ctor_get(v_x_4444_, 0);
v___x_4450_ = ((size_t)31ULL);
v___x_4451_ = lean_usize_land(v_x_4445_, v___x_4450_);
v_j_4452_ = lean_usize_to_nat(v___x_4451_);
v___x_4453_ = lean_array_get_size(v_es_4449_);
v___x_4454_ = lean_nat_dec_lt(v_j_4452_, v___x_4453_);
if (v___x_4454_ == 0)
{
lean_dec(v_j_4452_);
lean_dec(v_x_4448_);
lean_dec_ref(v_x_4447_);
return v_x_4444_;
}
else
{
lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4504_; 
lean_inc_ref(v_es_4449_);
v_isSharedCheck_4504_ = !lean_is_exclusive(v_x_4444_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; 
v_unused_4505_ = lean_ctor_get(v_x_4444_, 0);
lean_dec(v_unused_4505_);
v___x_4456_ = v_x_4444_;
v_isShared_4457_ = v_isSharedCheck_4504_;
goto v_resetjp_4455_;
}
else
{
lean_dec(v_x_4444_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4504_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v_v_4458_; lean_object* v___x_4459_; lean_object* v_xs_x27_4460_; lean_object* v___y_4462_; 
v_v_4458_ = lean_array_fget(v_es_4449_, v_j_4452_);
v___x_4459_ = lean_box(0);
v_xs_x27_4460_ = lean_array_fset(v_es_4449_, v_j_4452_, v___x_4459_);
switch(lean_obj_tag(v_v_4458_))
{
case 0:
{
lean_object* v_key_4467_; lean_object* v_val_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4489_; 
v_key_4467_ = lean_ctor_get(v_v_4458_, 0);
v_val_4468_ = lean_ctor_get(v_v_4458_, 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_v_4458_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4470_ = v_v_4458_;
v_isShared_4471_ = v_isSharedCheck_4489_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_val_4468_);
lean_inc(v_key_4467_);
lean_dec(v_v_4458_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4489_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
uint8_t v___y_4473_; lean_object* v_fst_4479_; lean_object* v_snd_4480_; lean_object* v_fst_4481_; lean_object* v_snd_4482_; size_t v___x_4483_; size_t v___x_4484_; uint8_t v___x_4485_; 
v_fst_4479_ = lean_ctor_get(v_x_4447_, 0);
v_snd_4480_ = lean_ctor_get(v_x_4447_, 1);
v_fst_4481_ = lean_ctor_get(v_key_4467_, 0);
v_snd_4482_ = lean_ctor_get(v_key_4467_, 1);
v___x_4483_ = lean_ptr_addr(v_fst_4479_);
v___x_4484_ = lean_ptr_addr(v_fst_4481_);
v___x_4485_ = lean_usize_dec_eq(v___x_4483_, v___x_4484_);
if (v___x_4485_ == 0)
{
v___y_4473_ = v___x_4485_;
goto v___jp_4472_;
}
else
{
size_t v___x_4486_; size_t v___x_4487_; uint8_t v___x_4488_; 
v___x_4486_ = lean_ptr_addr(v_snd_4480_);
v___x_4487_ = lean_ptr_addr(v_snd_4482_);
v___x_4488_ = lean_usize_dec_eq(v___x_4486_, v___x_4487_);
v___y_4473_ = v___x_4488_;
goto v___jp_4472_;
}
v___jp_4472_:
{
if (v___y_4473_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_del_object(v___x_4470_);
v___x_4474_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4467_, v_val_4468_, v_x_4447_, v_x_4448_);
v___x_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
v___y_4462_ = v___x_4475_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4477_; 
lean_dec(v_val_4468_);
lean_dec(v_key_4467_);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 1, v_x_4448_);
lean_ctor_set(v___x_4470_, 0, v_x_4447_);
v___x_4477_ = v___x_4470_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_x_4447_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_x_4448_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
v___y_4462_ = v___x_4477_;
goto v___jp_4461_;
}
}
}
}
}
case 1:
{
lean_object* v_node_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4502_; 
v_node_4490_ = lean_ctor_get(v_v_4458_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_v_4458_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4492_ = v_v_4458_;
v_isShared_4493_ = v_isSharedCheck_4502_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_node_4490_);
lean_dec(v_v_4458_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4502_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
size_t v___x_4494_; size_t v___x_4495_; size_t v___x_4496_; size_t v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4494_ = ((size_t)5ULL);
v___x_4495_ = lean_usize_shift_right(v_x_4445_, v___x_4494_);
v___x_4496_ = ((size_t)1ULL);
v___x_4497_ = lean_usize_add(v_x_4446_, v___x_4496_);
v___x_4498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4490_, v___x_4495_, v___x_4497_, v_x_4447_, v_x_4448_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4498_);
v___x_4500_ = v___x_4492_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
v___y_4462_ = v___x_4500_;
goto v___jp_4461_;
}
}
}
default: 
{
lean_object* v___x_4503_; 
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v_x_4447_);
lean_ctor_set(v___x_4503_, 1, v_x_4448_);
v___y_4462_ = v___x_4503_;
goto v___jp_4461_;
}
}
v___jp_4461_:
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4463_ = lean_array_fset(v_xs_x27_4460_, v_j_4452_, v___y_4462_);
lean_dec(v_j_4452_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 0, v___x_4463_);
v___x_4465_ = v___x_4456_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
else
{
lean_object* v_ks_4506_; lean_object* v_vs_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4527_; 
v_ks_4506_ = lean_ctor_get(v_x_4444_, 0);
v_vs_4507_ = lean_ctor_get(v_x_4444_, 1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_x_4444_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4509_ = v_x_4444_;
v_isShared_4510_ = v_isSharedCheck_4527_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_vs_4507_);
lean_inc(v_ks_4506_);
lean_dec(v_x_4444_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4527_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_ks_4506_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_vs_4507_);
v___x_4512_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v_newNode_4513_; uint8_t v___y_4515_; size_t v___x_4521_; uint8_t v___x_4522_; 
v_newNode_4513_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4512_, v_x_4447_, v_x_4448_);
v___x_4521_ = ((size_t)7ULL);
v___x_4522_ = lean_usize_dec_le(v___x_4521_, v_x_4446_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4523_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4513_);
v___x_4524_ = lean_unsigned_to_nat(4u);
v___x_4525_ = lean_nat_dec_lt(v___x_4523_, v___x_4524_);
lean_dec(v___x_4523_);
v___y_4515_ = v___x_4525_;
goto v___jp_4514_;
}
else
{
v___y_4515_ = v___x_4522_;
goto v___jp_4514_;
}
v___jp_4514_:
{
if (v___y_4515_ == 0)
{
lean_object* v_ks_4516_; lean_object* v_vs_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v_ks_4516_ = lean_ctor_get(v_newNode_4513_, 0);
lean_inc_ref(v_ks_4516_);
v_vs_4517_ = lean_ctor_get(v_newNode_4513_, 1);
lean_inc_ref(v_vs_4517_);
lean_dec_ref(v_newNode_4513_);
v___x_4518_ = lean_unsigned_to_nat(0u);
v___x_4519_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4520_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4446_, v_ks_4516_, v_vs_4517_, v___x_4518_, v___x_4519_);
lean_dec_ref(v_vs_4517_);
lean_dec_ref(v_ks_4516_);
return v___x_4520_;
}
else
{
return v_newNode_4513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4528_, lean_object* v_keys_4529_, lean_object* v_vals_4530_, lean_object* v_i_4531_, lean_object* v_entries_4532_){
_start:
{
lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4533_ = lean_array_get_size(v_keys_4529_);
v___x_4534_ = lean_nat_dec_lt(v_i_4531_, v___x_4533_);
if (v___x_4534_ == 0)
{
lean_dec(v_i_4531_);
return v_entries_4532_;
}
else
{
lean_object* v_k_4535_; lean_object* v_fst_4536_; lean_object* v_snd_4537_; lean_object* v_v_4538_; size_t v___x_4539_; size_t v___x_4540_; size_t v___x_4541_; uint64_t v___x_4542_; size_t v___x_4543_; size_t v___x_4544_; uint64_t v___x_4545_; uint64_t v___x_4546_; size_t v_h_4547_; size_t v___x_4548_; lean_object* v___x_4549_; size_t v___x_4550_; size_t v___x_4551_; size_t v___x_4552_; size_t v_h_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_k_4535_ = lean_array_fget_borrowed(v_keys_4529_, v_i_4531_);
v_fst_4536_ = lean_ctor_get(v_k_4535_, 0);
v_snd_4537_ = lean_ctor_get(v_k_4535_, 1);
v_v_4538_ = lean_array_fget_borrowed(v_vals_4530_, v_i_4531_);
v___x_4539_ = lean_ptr_addr(v_fst_4536_);
v___x_4540_ = ((size_t)3ULL);
v___x_4541_ = lean_usize_shift_right(v___x_4539_, v___x_4540_);
v___x_4542_ = lean_usize_to_uint64(v___x_4541_);
v___x_4543_ = lean_ptr_addr(v_snd_4537_);
v___x_4544_ = lean_usize_shift_right(v___x_4543_, v___x_4540_);
v___x_4545_ = lean_usize_to_uint64(v___x_4544_);
v___x_4546_ = lean_uint64_mix_hash(v___x_4542_, v___x_4545_);
v_h_4547_ = lean_uint64_to_usize(v___x_4546_);
v___x_4548_ = ((size_t)5ULL);
v___x_4549_ = lean_unsigned_to_nat(1u);
v___x_4550_ = ((size_t)1ULL);
v___x_4551_ = lean_usize_sub(v_depth_4528_, v___x_4550_);
v___x_4552_ = lean_usize_mul(v___x_4548_, v___x_4551_);
v_h_4553_ = lean_usize_shift_right(v_h_4547_, v___x_4552_);
v___x_4554_ = lean_nat_add(v_i_4531_, v___x_4549_);
lean_dec(v_i_4531_);
lean_inc(v_v_4538_);
lean_inc(v_k_4535_);
v___x_4555_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4532_, v_h_4553_, v_depth_4528_, v_k_4535_, v_v_4538_);
v_i_4531_ = v___x_4554_;
v_entries_4532_ = v___x_4555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4557_, lean_object* v_keys_4558_, lean_object* v_vals_4559_, lean_object* v_i_4560_, lean_object* v_entries_4561_){
_start:
{
size_t v_depth_boxed_4562_; lean_object* v_res_4563_; 
v_depth_boxed_4562_ = lean_unbox_usize(v_depth_4557_);
lean_dec(v_depth_4557_);
v_res_4563_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4562_, v_keys_4558_, v_vals_4559_, v_i_4560_, v_entries_4561_);
lean_dec_ref(v_vals_4559_);
lean_dec_ref(v_keys_4558_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4564_, lean_object* v_x_4565_, lean_object* v_x_4566_, lean_object* v_x_4567_, lean_object* v_x_4568_){
_start:
{
size_t v_x_2969__boxed_4569_; size_t v_x_2970__boxed_4570_; lean_object* v_res_4571_; 
v_x_2969__boxed_4569_ = lean_unbox_usize(v_x_4565_);
lean_dec(v_x_4565_);
v_x_2970__boxed_4570_ = lean_unbox_usize(v_x_4566_);
lean_dec(v_x_4566_);
v_res_4571_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4564_, v_x_2969__boxed_4569_, v_x_2970__boxed_4570_, v_x_4567_, v_x_4568_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4572_, lean_object* v_x_4573_, lean_object* v_x_4574_){
_start:
{
lean_object* v_fst_4575_; lean_object* v_snd_4576_; size_t v___x_4577_; size_t v___x_4578_; size_t v___x_4579_; uint64_t v___x_4580_; size_t v___x_4581_; size_t v___x_4582_; uint64_t v___x_4583_; uint64_t v___x_4584_; size_t v___x_4585_; size_t v___x_4586_; lean_object* v___x_4587_; 
v_fst_4575_ = lean_ctor_get(v_x_4573_, 0);
v_snd_4576_ = lean_ctor_get(v_x_4573_, 1);
v___x_4577_ = lean_ptr_addr(v_fst_4575_);
v___x_4578_ = ((size_t)3ULL);
v___x_4579_ = lean_usize_shift_right(v___x_4577_, v___x_4578_);
v___x_4580_ = lean_usize_to_uint64(v___x_4579_);
v___x_4581_ = lean_ptr_addr(v_snd_4576_);
v___x_4582_ = lean_usize_shift_right(v___x_4581_, v___x_4578_);
v___x_4583_ = lean_usize_to_uint64(v___x_4582_);
v___x_4584_ = lean_uint64_mix_hash(v___x_4580_, v___x_4583_);
v___x_4585_ = lean_uint64_to_usize(v___x_4584_);
v___x_4586_ = ((size_t)1ULL);
v___x_4587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4572_, v___x_4585_, v___x_4586_, v_x_4573_, v_x_4574_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4588_, lean_object* v_t_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v___x_4596_; lean_object* v_defEqI_4597_; lean_object* v_key_4598_; lean_object* v___x_4599_; 
v___x_4596_ = lean_st_ref_get(v_a_4590_);
v_defEqI_4597_ = lean_ctor_get(v___x_4596_, 6);
lean_inc_ref(v_defEqI_4597_);
lean_dec(v___x_4596_);
lean_inc_ref(v_t_4589_);
lean_inc_ref(v_s_4588_);
v_key_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4598_, 0, v_s_4588_);
lean_ctor_set(v_key_4598_, 1, v_t_4589_);
v___x_4599_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4597_, v_key_4598_);
lean_dec_ref(v_defEqI_4597_);
if (lean_obj_tag(v___x_4599_) == 1)
{
lean_object* v_val_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec_ref_known(v_key_4598_, 2);
lean_dec_ref(v_t_4589_);
lean_dec_ref(v_s_4588_);
v_val_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_val_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
lean_ctor_set_tag(v___x_4602_, 0);
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_val_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
lean_object* v___x_4608_; 
lean_dec(v___x_4599_);
v___x_4608_ = l_Lean_Meta_isDefEqI(v_s_4588_, v_t_4589_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4638_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4611_ = v___x_4608_;
v_isShared_4612_ = v_isSharedCheck_4638_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4638_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; lean_object* v_share_4614_; lean_object* v_maxFVar_4615_; lean_object* v_proofInstInfo_4616_; lean_object* v_inferType_4617_; lean_object* v_getLevel_4618_; lean_object* v_congrInfo_4619_; lean_object* v_defEqI_4620_; lean_object* v_extensions_4621_; lean_object* v_issues_4622_; lean_object* v_canon_4623_; lean_object* v_instanceOverrides_4624_; uint8_t v_debug_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4637_; 
v___x_4613_ = lean_st_ref_take(v_a_4590_);
v_share_4614_ = lean_ctor_get(v___x_4613_, 0);
v_maxFVar_4615_ = lean_ctor_get(v___x_4613_, 1);
v_proofInstInfo_4616_ = lean_ctor_get(v___x_4613_, 2);
v_inferType_4617_ = lean_ctor_get(v___x_4613_, 3);
v_getLevel_4618_ = lean_ctor_get(v___x_4613_, 4);
v_congrInfo_4619_ = lean_ctor_get(v___x_4613_, 5);
v_defEqI_4620_ = lean_ctor_get(v___x_4613_, 6);
v_extensions_4621_ = lean_ctor_get(v___x_4613_, 7);
v_issues_4622_ = lean_ctor_get(v___x_4613_, 8);
v_canon_4623_ = lean_ctor_get(v___x_4613_, 9);
v_instanceOverrides_4624_ = lean_ctor_get(v___x_4613_, 10);
v_debug_4625_ = lean_ctor_get_uint8(v___x_4613_, sizeof(void*)*11);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4627_ = v___x_4613_;
v_isShared_4628_ = v_isSharedCheck_4637_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_instanceOverrides_4624_);
lean_inc(v_canon_4623_);
lean_inc(v_issues_4622_);
lean_inc(v_extensions_4621_);
lean_inc(v_defEqI_4620_);
lean_inc(v_congrInfo_4619_);
lean_inc(v_getLevel_4618_);
lean_inc(v_inferType_4617_);
lean_inc(v_proofInstInfo_4616_);
lean_inc(v_maxFVar_4615_);
lean_inc(v_share_4614_);
lean_dec(v___x_4613_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4637_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4629_; lean_object* v___x_4631_; 
lean_inc(v_a_4609_);
v___x_4629_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4620_, v_key_4598_, v_a_4609_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 6, v___x_4629_);
v___x_4631_ = v___x_4627_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_share_4614_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_maxFVar_4615_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_proofInstInfo_4616_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_inferType_4617_);
lean_ctor_set(v_reuseFailAlloc_4636_, 4, v_getLevel_4618_);
lean_ctor_set(v_reuseFailAlloc_4636_, 5, v_congrInfo_4619_);
lean_ctor_set(v_reuseFailAlloc_4636_, 6, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4636_, 7, v_extensions_4621_);
lean_ctor_set(v_reuseFailAlloc_4636_, 8, v_issues_4622_);
lean_ctor_set(v_reuseFailAlloc_4636_, 9, v_canon_4623_);
lean_ctor_set(v_reuseFailAlloc_4636_, 10, v_instanceOverrides_4624_);
lean_ctor_set_uint8(v_reuseFailAlloc_4636_, sizeof(void*)*11, v_debug_4625_);
v___x_4631_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4632_ = lean_st_ref_set(v_a_4590_, v___x_4631_);
if (v_isShared_4612_ == 0)
{
v___x_4634_ = v___x_4611_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4609_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4598_, 2);
return v___x_4608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4639_, lean_object* v_t_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4639_, v_t_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4648_, lean_object* v_t_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4648_, v_t_4649_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4658_, lean_object* v_t_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Meta_Sym_isDefEqI(v_s_4658_, v_t_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4668_, lean_object* v_x_4669_, lean_object* v_x_4670_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4669_, v_x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4672_, lean_object* v_x_4673_, lean_object* v_x_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4672_, v_x_4673_, v_x_4674_);
lean_dec_ref(v_x_4674_);
lean_dec_ref(v_x_4673_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4676_, lean_object* v_x_4677_, lean_object* v_x_4678_, lean_object* v_x_4679_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4677_, v_x_4678_, v_x_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4681_, lean_object* v_x_4682_, size_t v_x_4683_, lean_object* v_x_4684_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4682_, v_x_4683_, v_x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4686_, lean_object* v_x_4687_, lean_object* v_x_4688_, lean_object* v_x_4689_){
_start:
{
size_t v_x_3271__boxed_4690_; lean_object* v_res_4691_; 
v_x_3271__boxed_4690_ = lean_unbox_usize(v_x_4688_);
lean_dec(v_x_4688_);
v_res_4691_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4686_, v_x_4687_, v_x_3271__boxed_4690_, v_x_4689_);
lean_dec_ref(v_x_4689_);
lean_dec_ref(v_x_4687_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4692_, lean_object* v_x_4693_, size_t v_x_4694_, size_t v_x_4695_, lean_object* v_x_4696_, lean_object* v_x_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4693_, v_x_4694_, v_x_4695_, v_x_4696_, v_x_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4699_, lean_object* v_x_4700_, lean_object* v_x_4701_, lean_object* v_x_4702_, lean_object* v_x_4703_, lean_object* v_x_4704_){
_start:
{
size_t v_x_3282__boxed_4705_; size_t v_x_3283__boxed_4706_; lean_object* v_res_4707_; 
v_x_3282__boxed_4705_ = lean_unbox_usize(v_x_4701_);
lean_dec(v_x_4701_);
v_x_3283__boxed_4706_ = lean_unbox_usize(v_x_4702_);
lean_dec(v_x_4702_);
v_res_4707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4699_, v_x_4700_, v_x_3282__boxed_4705_, v_x_3283__boxed_4706_, v_x_4703_, v_x_4704_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4708_, lean_object* v_keys_4709_, lean_object* v_vals_4710_, lean_object* v_heq_4711_, lean_object* v_i_4712_, lean_object* v_k_4713_){
_start:
{
lean_object* v___x_4714_; 
v___x_4714_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4709_, v_vals_4710_, v_i_4712_, v_k_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4715_, lean_object* v_keys_4716_, lean_object* v_vals_4717_, lean_object* v_heq_4718_, lean_object* v_i_4719_, lean_object* v_k_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4715_, v_keys_4716_, v_vals_4717_, v_heq_4718_, v_i_4719_, v_k_4720_);
lean_dec_ref(v_k_4720_);
lean_dec_ref(v_vals_4717_);
lean_dec_ref(v_keys_4716_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4722_, lean_object* v_n_4723_, lean_object* v_k_4724_, lean_object* v_v_4725_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4723_, v_k_4724_, v_v_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4727_, size_t v_depth_4728_, lean_object* v_keys_4729_, lean_object* v_vals_4730_, lean_object* v_heq_4731_, lean_object* v_i_4732_, lean_object* v_entries_4733_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4728_, v_keys_4729_, v_vals_4730_, v_i_4732_, v_entries_4733_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4735_, lean_object* v_depth_4736_, lean_object* v_keys_4737_, lean_object* v_vals_4738_, lean_object* v_heq_4739_, lean_object* v_i_4740_, lean_object* v_entries_4741_){
_start:
{
size_t v_depth_boxed_4742_; lean_object* v_res_4743_; 
v_depth_boxed_4742_ = lean_unbox_usize(v_depth_4736_);
lean_dec(v_depth_4736_);
v_res_4743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4735_, v_depth_boxed_4742_, v_keys_4737_, v_vals_4738_, v_heq_4739_, v_i_4740_, v_entries_4741_);
lean_dec_ref(v_vals_4738_);
lean_dec_ref(v_keys_4737_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_, lean_object* v_x_4747_, lean_object* v_x_4748_){
_start:
{
lean_object* v___x_4749_; 
v___x_4749_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4745_, v_x_4746_, v_x_4747_, v_x_4748_);
return v___x_4749_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___f_4751_; 
v___x_4750_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4751_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4751_, 0, v___x_4750_);
return v___f_4751_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_4752_; lean_object* v___f_4753_; 
v___x_4752_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4753_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4753_, 0, v___x_4752_);
return v___f_4753_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2(void){
_start:
{
lean_object* v___f_4754_; lean_object* v___f_4755_; lean_object* v___x_4756_; 
v___f_4754_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v___f_4755_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_4756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___f_4755_);
lean_ctor_set(v___x_4756_, 1, v___f_4754_);
return v___x_4756_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3(void){
_start:
{
lean_object* v___x_4757_; lean_object* v___f_4758_; 
v___x_4757_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4758_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4758_, 0, v___x_4757_);
return v___f_4758_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4(void){
_start:
{
lean_object* v___x_4759_; lean_object* v___f_4760_; 
v___x_4759_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4760_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4760_, 0, v___x_4759_);
return v___f_4760_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5(void){
_start:
{
lean_object* v___f_4761_; lean_object* v___f_4762_; lean_object* v___x_4763_; 
v___f_4761_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4);
v___f_4762_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3);
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___f_4762_);
lean_ctor_set(v___x_4763_, 1, v___f_4761_);
return v___x_4763_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_4764_; lean_object* v___f_4765_; 
v___x_4764_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4765_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4765_, 0, v___x_4764_);
return v___f_4765_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___f_4767_; 
v___x_4766_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4767_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4767_, 0, v___x_4766_);
return v___f_4767_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_4768_; lean_object* v___f_4769_; lean_object* v___x_4770_; 
v___f_4768_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_4769_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_4770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___f_4769_);
lean_ctor_set(v___x_4770_, 1, v___f_4768_);
return v___x_4770_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___f_4772_; 
v___x_4771_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4772_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4772_, 0, v___x_4771_);
return v___f_4772_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___f_4774_; 
v___x_4773_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4774_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4774_, 0, v___x_4773_);
return v___f_4774_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_4775_; lean_object* v___f_4776_; lean_object* v___x_4777_; 
v___f_4775_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_4776_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___f_4776_);
lean_ctor_set(v___x_4777_, 1, v___f_4775_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4782_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4783_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4784_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4785_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4784_, v___x_4783_, v___x_4782_);
return v___x_4785_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___f_4787_; lean_object* v___f_4788_; lean_object* v___x_4789_; 
v___x_4786_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_4787_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4788_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4789_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4788_, v___f_4787_, v___x_4786_);
return v___x_4789_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4790_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_4791_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4792_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4793_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4792_, v___x_4791_, v___x_4790_);
return v___x_4793_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___f_4795_; lean_object* v___f_4796_; lean_object* v___x_4797_; 
v___x_4794_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18);
v___f_4795_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4796_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4797_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4796_, v___f_4795_, v___x_4794_);
return v___x_4797_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___f_4800_; 
v___x_4798_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4799_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4800_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4800_, 0, v___x_4799_);
lean_closure_set(v___f_4800_, 1, v___x_4798_);
return v___f_4800_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21(void){
_start:
{
lean_object* v___f_4801_; lean_object* v___f_4802_; lean_object* v___f_4803_; 
v___f_4801_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4802_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20);
v___f_4803_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4803_, 0, v___f_4802_);
lean_closure_set(v___f_4803_, 1, v___f_4801_);
return v___f_4803_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__22));
v___x_4806_ = l_Lean_stringToMessageData(v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4807_){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v_toApplicative_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4877_; 
v___x_4808_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4809_ = l_StateRefT_x27_instMonad___redArg(v___x_4808_);
v_toApplicative_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4877_ == 0)
{
lean_object* v_unused_4878_; 
v_unused_4878_ = lean_ctor_get(v___x_4809_, 1);
lean_dec(v_unused_4878_);
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4877_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_toApplicative_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4877_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v_toFunctor_4814_; lean_object* v_toSeq_4815_; lean_object* v_toSeqLeft_4816_; lean_object* v_toSeqRight_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4875_; 
v_toFunctor_4814_ = lean_ctor_get(v_toApplicative_4810_, 0);
v_toSeq_4815_ = lean_ctor_get(v_toApplicative_4810_, 2);
v_toSeqLeft_4816_ = lean_ctor_get(v_toApplicative_4810_, 3);
v_toSeqRight_4817_ = lean_ctor_get(v_toApplicative_4810_, 4);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_toApplicative_4810_);
if (v_isSharedCheck_4875_ == 0)
{
lean_object* v_unused_4876_; 
v_unused_4876_ = lean_ctor_get(v_toApplicative_4810_, 1);
lean_dec(v_unused_4876_);
v___x_4819_ = v_toApplicative_4810_;
v_isShared_4820_ = v_isSharedCheck_4875_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_toSeqRight_4817_);
lean_inc(v_toSeqLeft_4816_);
lean_inc(v_toSeq_4815_);
lean_inc(v_toFunctor_4814_);
lean_dec(v_toApplicative_4810_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4875_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___f_4821_; lean_object* v___f_4822_; lean_object* v___f_4823_; lean_object* v___f_4824_; lean_object* v___x_4825_; lean_object* v___f_4826_; lean_object* v___f_4827_; lean_object* v___f_4828_; lean_object* v___x_4830_; 
v___f_4821_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4822_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4814_);
v___f_4823_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4823_, 0, v_toFunctor_4814_);
v___f_4824_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4824_, 0, v_toFunctor_4814_);
v___x_4825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___f_4823_);
lean_ctor_set(v___x_4825_, 1, v___f_4824_);
v___f_4826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4826_, 0, v_toSeqRight_4817_);
v___f_4827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4827_, 0, v_toSeqLeft_4816_);
v___f_4828_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4828_, 0, v_toSeq_4815_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 4, v___f_4826_);
lean_ctor_set(v___x_4819_, 3, v___f_4827_);
lean_ctor_set(v___x_4819_, 2, v___f_4828_);
lean_ctor_set(v___x_4819_, 1, v___f_4821_);
lean_ctor_set(v___x_4819_, 0, v___x_4825_);
v___x_4830_ = v___x_4819_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4825_);
lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___f_4821_);
lean_ctor_set(v_reuseFailAlloc_4874_, 2, v___f_4828_);
lean_ctor_set(v_reuseFailAlloc_4874_, 3, v___f_4827_);
lean_ctor_set(v_reuseFailAlloc_4874_, 4, v___f_4826_);
v___x_4830_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4832_; 
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 1, v___f_4822_);
lean_ctor_set(v___x_4812_, 0, v___x_4830_);
v___x_4832_ = v___x_4812_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4830_);
lean_ctor_set(v_reuseFailAlloc_4873_, 1, v___f_4822_);
v___x_4832_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
lean_object* v___x_4833_; lean_object* v_toApplicative_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4871_; 
v___x_4833_ = l_StateRefT_x27_instMonad___redArg(v___x_4832_);
v_toApplicative_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; 
v_unused_4872_ = lean_ctor_get(v___x_4833_, 1);
lean_dec(v_unused_4872_);
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4871_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_toApplicative_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4871_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v_toFunctor_4838_; lean_object* v_toSeq_4839_; lean_object* v_toSeqLeft_4840_; lean_object* v_toSeqRight_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4869_; 
v_toFunctor_4838_ = lean_ctor_get(v_toApplicative_4834_, 0);
v_toSeq_4839_ = lean_ctor_get(v_toApplicative_4834_, 2);
v_toSeqLeft_4840_ = lean_ctor_get(v_toApplicative_4834_, 3);
v_toSeqRight_4841_ = lean_ctor_get(v_toApplicative_4834_, 4);
v_isSharedCheck_4869_ = !lean_is_exclusive(v_toApplicative_4834_);
if (v_isSharedCheck_4869_ == 0)
{
lean_object* v_unused_4870_; 
v_unused_4870_ = lean_ctor_get(v_toApplicative_4834_, 1);
lean_dec(v_unused_4870_);
v___x_4843_ = v_toApplicative_4834_;
v_isShared_4844_ = v_isSharedCheck_4869_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_toSeqRight_4841_);
lean_inc(v_toSeqLeft_4840_);
lean_inc(v_toSeq_4839_);
lean_inc(v_toFunctor_4838_);
lean_dec(v_toApplicative_4834_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4869_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___f_4845_; lean_object* v___f_4846_; lean_object* v___f_4847_; lean_object* v___f_4848_; lean_object* v___x_4849_; lean_object* v___f_4850_; lean_object* v___f_4851_; lean_object* v___f_4852_; lean_object* v___x_4854_; 
v___f_4845_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4846_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4838_);
v___f_4847_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4847_, 0, v_toFunctor_4838_);
v___f_4848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4848_, 0, v_toFunctor_4838_);
v___x_4849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4849_, 0, v___f_4847_);
lean_ctor_set(v___x_4849_, 1, v___f_4848_);
v___f_4850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4850_, 0, v_toSeqRight_4841_);
v___f_4851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4851_, 0, v_toSeqLeft_4840_);
v___f_4852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4852_, 0, v_toSeq_4839_);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 4, v___f_4850_);
lean_ctor_set(v___x_4843_, 3, v___f_4851_);
lean_ctor_set(v___x_4843_, 2, v___f_4852_);
lean_ctor_set(v___x_4843_, 1, v___f_4845_);
lean_ctor_set(v___x_4843_, 0, v___x_4849_);
v___x_4854_ = v___x_4843_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4849_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v___f_4845_);
lean_ctor_set(v_reuseFailAlloc_4868_, 2, v___f_4852_);
lean_ctor_set(v_reuseFailAlloc_4868_, 3, v___f_4851_);
lean_ctor_set(v_reuseFailAlloc_4868_, 4, v___f_4850_);
v___x_4854_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4856_; 
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___f_4846_);
lean_ctor_set(v___x_4836_, 0, v___x_4854_);
v___x_4856_ = v___x_4836_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v___f_4846_);
v___x_4856_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v_toMonadRef_4861_; lean_object* v___f_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4857_ = l_StateRefT_x27_instMonad___redArg(v___x_4856_);
v___x_4858_ = l_ReaderT_instMonad___redArg(v___x_4857_);
v___x_4859_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___x_4860_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19);
v_toMonadRef_4861_ = lean_ctor_get(v___x_4860_, 0);
v___f_4862_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21);
lean_inc_ref(v___x_4858_);
v___x_4863_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4862_, v___x_4858_);
lean_inc_ref(v_toMonadRef_4861_);
v___x_4864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4859_);
lean_ctor_set(v___x_4864_, 1, v_toMonadRef_4861_);
lean_ctor_set(v___x_4864_, 2, v___x_4863_);
v___x_4865_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_4866_ = l_Lean_throwError___redArg(v___x_4858_, v___x_4864_, v___x_4865_);
return v___x_4866_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4879_, lean_object* v_extensions_4880_){
_start:
{
lean_object* v_id_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v_id_4882_ = lean_ctor_get(v_ext_4879_, 0);
v___x_4883_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4884_ = lean_array_get_borrowed(v___x_4883_, v_extensions_4880_, v_id_4882_);
lean_inc(v___x_4884_);
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4886_, lean_object* v_extensions_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4886_, v_extensions_4887_);
lean_dec_ref(v_extensions_4887_);
lean_dec_ref(v_ext_4886_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_4890_, lean_object* v_ext_4891_, lean_object* v_extensions_4892_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4891_, v_extensions_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_4895_, lean_object* v_ext_4896_, lean_object* v_extensions_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_4895_, v_ext_4896_, v_extensions_4897_);
lean_dec_ref(v_extensions_4897_);
lean_dec_ref(v_ext_4896_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v___x_4904_; lean_object* v_extensions_4905_; lean_object* v___x_4906_; 
v___x_4904_ = lean_st_ref_get(v_a_4901_);
v_extensions_4905_ = lean_ctor_get(v___x_4904_, 7);
lean_inc_ref(v_extensions_4905_);
lean_dec(v___x_4904_);
v___x_4906_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4900_, v_extensions_4905_);
lean_dec_ref(v_extensions_4905_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4906_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4906_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4927_; 
v_a_4915_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4917_ = v___x_4906_;
v_isShared_4918_ = v_isSharedCheck_4927_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4906_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4927_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v_ref_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4925_; 
v_ref_4919_ = lean_ctor_get(v_a_4902_, 5);
v___x_4920_ = lean_io_error_to_string(v_a_4915_);
v___x_4921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
v___x_4922_ = l_Lean_MessageData_ofFormat(v___x_4921_);
lean_inc(v_ref_4919_);
v___x_4923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4923_, 0, v_ref_4919_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4923_);
v___x_4925_ = v___x_4917_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4928_, v_a_4929_, v_a_4930_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_ext_4928_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_4933_, lean_object* v_ext_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v___x_4942_; 
v___x_4942_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4934_, v_a_4936_, v_a_4939_);
return v___x_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_4943_, lean_object* v_ext_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_4943_, v_ext_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec_ref(v_ext_4944_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_4953_, lean_object* v_f_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v_share_4958_; lean_object* v_maxFVar_4959_; lean_object* v_proofInstInfo_4960_; lean_object* v_inferType_4961_; lean_object* v_getLevel_4962_; lean_object* v_congrInfo_4963_; lean_object* v_defEqI_4964_; lean_object* v_extensions_4965_; lean_object* v_issues_4966_; lean_object* v_canon_4967_; lean_object* v_instanceOverrides_4968_; uint8_t v_debug_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4988_; 
v___x_4957_ = lean_st_ref_take(v_a_4955_);
v_share_4958_ = lean_ctor_get(v___x_4957_, 0);
v_maxFVar_4959_ = lean_ctor_get(v___x_4957_, 1);
v_proofInstInfo_4960_ = lean_ctor_get(v___x_4957_, 2);
v_inferType_4961_ = lean_ctor_get(v___x_4957_, 3);
v_getLevel_4962_ = lean_ctor_get(v___x_4957_, 4);
v_congrInfo_4963_ = lean_ctor_get(v___x_4957_, 5);
v_defEqI_4964_ = lean_ctor_get(v___x_4957_, 6);
v_extensions_4965_ = lean_ctor_get(v___x_4957_, 7);
v_issues_4966_ = lean_ctor_get(v___x_4957_, 8);
v_canon_4967_ = lean_ctor_get(v___x_4957_, 9);
v_instanceOverrides_4968_ = lean_ctor_get(v___x_4957_, 10);
v_debug_4969_ = lean_ctor_get_uint8(v___x_4957_, sizeof(void*)*11);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4971_ = v___x_4957_;
v_isShared_4972_ = v_isSharedCheck_4988_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_instanceOverrides_4968_);
lean_inc(v_canon_4967_);
lean_inc(v_issues_4966_);
lean_inc(v_extensions_4965_);
lean_inc(v_defEqI_4964_);
lean_inc(v_congrInfo_4963_);
lean_inc(v_getLevel_4962_);
lean_inc(v_inferType_4961_);
lean_inc(v_proofInstInfo_4960_);
lean_inc(v_maxFVar_4959_);
lean_inc(v_share_4958_);
lean_dec(v___x_4957_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4988_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v_id_4973_; lean_object* v___x_4974_; lean_object* v___y_4976_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v_id_4973_ = lean_ctor_get(v_ext_4953_, 0);
v___x_4974_ = lean_box(0);
v___x_4982_ = lean_array_get_size(v_extensions_4965_);
v___x_4983_ = lean_nat_dec_lt(v_id_4973_, v___x_4982_);
if (v___x_4983_ == 0)
{
lean_dec(v_f_4954_);
v___y_4976_ = v_extensions_4965_;
goto v___jp_4975_;
}
else
{
lean_object* v_v_4984_; lean_object* v_xs_x27_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v_v_4984_ = lean_array_fget(v_extensions_4965_, v_id_4973_);
v_xs_x27_4985_ = lean_array_fset(v_extensions_4965_, v_id_4973_, v___x_4974_);
v___x_4986_ = lean_apply_1(v_f_4954_, v_v_4984_);
v___x_4987_ = lean_array_fset(v_xs_x27_4985_, v_id_4973_, v___x_4986_);
v___y_4976_ = v___x_4987_;
goto v___jp_4975_;
}
v___jp_4975_:
{
lean_object* v___x_4978_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 7, v___y_4976_);
v___x_4978_ = v___x_4971_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_share_4958_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_maxFVar_4959_);
lean_ctor_set(v_reuseFailAlloc_4981_, 2, v_proofInstInfo_4960_);
lean_ctor_set(v_reuseFailAlloc_4981_, 3, v_inferType_4961_);
lean_ctor_set(v_reuseFailAlloc_4981_, 4, v_getLevel_4962_);
lean_ctor_set(v_reuseFailAlloc_4981_, 5, v_congrInfo_4963_);
lean_ctor_set(v_reuseFailAlloc_4981_, 6, v_defEqI_4964_);
lean_ctor_set(v_reuseFailAlloc_4981_, 7, v___y_4976_);
lean_ctor_set(v_reuseFailAlloc_4981_, 8, v_issues_4966_);
lean_ctor_set(v_reuseFailAlloc_4981_, 9, v_canon_4967_);
lean_ctor_set(v_reuseFailAlloc_4981_, 10, v_instanceOverrides_4968_);
lean_ctor_set_uint8(v_reuseFailAlloc_4981_, sizeof(void*)*11, v_debug_4969_);
v___x_4978_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = lean_st_ref_set(v_a_4955_, v___x_4978_);
v___x_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4974_);
return v___x_4980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_4989_, lean_object* v_f_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4989_, v_f_4990_, v_a_4991_);
lean_dec(v_a_4991_);
lean_dec_ref(v_ext_4989_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_4994_, lean_object* v_ext_4995_, lean_object* v_f_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4995_, v_f_4996_, v_a_4998_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5005_, lean_object* v_ext_5006_, lean_object* v_f_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5005_, v_ext_5006_, v_f_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
lean_dec_ref(v_ext_5006_);
return v_res_5015_;
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
