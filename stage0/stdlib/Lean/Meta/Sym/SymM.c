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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__2;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__4;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__6;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__8;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__10;
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.Sym.SymM"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.SymM.run"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "<SymM default value>"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1));
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed(lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg(){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1));
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___boxed(lean_object* v___dummy_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
return v_res_155_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object* v_00_u03c3_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg(){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg___boxed(lean_object* v___dummy_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_Sym_instInhabitedSymExtension___redArg();
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_));
v___x_169_ = lean_st_mk_ref(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object* v_ext_173_){
_start:
{
lean_inc_ref(v_ext_173_);
return v_ext_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object* v_ext_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(v_ext_174_);
lean_dec_ref(v_ext_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object* v_00_u03c3_176_, lean_object* v_ext_177_){
_start:
{
lean_inc_ref(v_ext_177_);
return v_ext_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object* v_00_u03c3_178_, lean_object* v_ext_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(v_00_u03c3_178_, v_ext_179_);
lean_dec_ref(v_ext_179_);
return v_res_180_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0));
v___x_183_ = lean_mk_io_user_error(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object* v_mkInitial_184_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_initializing();
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_mkInitial_184_);
v___x_187_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_189_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_190_ = lean_st_ref_get(v___x_189_);
v___x_191_ = lean_array_get_size(v___x_190_);
lean_dec(v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_mkInitial_184_);
v___x_193_ = lean_st_ref_take(v___x_189_);
lean_inc_ref(v___x_192_);
v___x_194_ = lean_array_push(v___x_193_, v___x_192_);
v___x_195_ = lean_st_ref_put(v___x_189_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_200_, lean_object* v_mkInitial_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_204_, lean_object* v_mkInitial_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_204_, v_mkInitial_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_208_, size_t v_i_209_, lean_object* v_bs_210_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_lt(v_i_209_, v_sz_208_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_bs_210_);
return v___x_213_;
}
else
{
lean_object* v_v_214_; lean_object* v_mkInitial_215_; lean_object* v___x_216_; lean_object* v_bs_x27_217_; lean_object* v___x_218_; 
v_v_214_ = lean_array_uget_borrowed(v_bs_210_, v_i_209_);
v_mkInitial_215_ = lean_ctor_get(v_v_214_, 1);
lean_inc_ref(v_mkInitial_215_);
v___x_216_ = lean_unsigned_to_nat(0u);
v_bs_x27_217_ = lean_array_uset(v_bs_210_, v_i_209_, v___x_216_);
v___x_218_ = lean_apply_1(v_mkInitial_215_, lean_box(0));
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_i_209_, v___x_220_);
v___x_222_ = lean_array_uset(v_bs_x27_217_, v_i_209_, v_a_219_);
v_i_209_ = v___x_221_;
v_bs_210_ = v___x_222_;
goto _start;
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v_bs_x27_217_);
v_a_224_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_218_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_218_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_bs_234_, lean_object* v___y_235_){
_start:
{
size_t v_sz_boxed_236_; size_t v_i_boxed_237_; lean_object* v_res_238_; 
v_sz_boxed_236_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_237_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_236_, v_i_boxed_237_, v_bs_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; size_t v_sz_242_; size_t v___x_243_; lean_object* v___x_244_; 
v___x_240_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_241_ = lean_st_ref_get(v___x_240_);
v_sz_242_ = lean_array_size(v___x_241_);
v___x_243_ = ((size_t)0ULL);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_242_, v___x_243_, v___x_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(lean_object* v_x_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_tag_nat(v_x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl___boxed(lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(v_x_257_);
lean_dec(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_259_, lean_object* v_k_260_){
_start:
{
switch(lean_obj_tag(v_t_259_))
{
case 0:
{
return v_k_260_;
}
case 1:
{
lean_object* v_prefixSize_261_; lean_object* v_suffixSize_262_; lean_object* v___x_263_; 
v_prefixSize_261_ = lean_ctor_get(v_t_259_, 0);
lean_inc(v_prefixSize_261_);
v_suffixSize_262_ = lean_ctor_get(v_t_259_, 1);
lean_inc(v_suffixSize_262_);
lean_dec_ref_known(v_t_259_, 2);
v___x_263_ = lean_apply_2(v_k_260_, v_prefixSize_261_, v_suffixSize_262_);
return v___x_263_;
}
default: 
{
lean_object* v_rewritable_264_; lean_object* v___x_265_; 
v_rewritable_264_ = lean_ctor_get(v_t_259_, 0);
lean_inc_ref(v_rewritable_264_);
lean_dec(v_t_259_);
v___x_265_ = lean_apply_1(v_k_260_, v_rewritable_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_266_, lean_object* v_ctorIdx_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_k_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_268_, v_k_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_272_, v_ctorIdx_273_, v_t_274_, v_h_275_, v_k_276_);
lean_dec(v_ctorIdx_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_278_, lean_object* v_none_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_278_, v_none_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_none_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_282_, v_none_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_286_, lean_object* v_fixedPrefix_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_286_, v_fixedPrefix_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_fixedPrefix_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_290_, v_fixedPrefix_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_294_, lean_object* v_interlaced_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_294_, v_interlaced_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_interlaced_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_298_, v_interlaced_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_302_, lean_object* v_congrTheorem_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_302_, v_congrTheorem_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_congrTheorem_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_306_, v_congrTheorem_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Expr_getAppFn(v_e_316_);
if (lean_obj_tag(v___x_322_) == 4)
{
lean_object* v_declName_323_; lean_object* v___x_324_; lean_object* v_env_325_; uint8_t v___x_326_; 
v_declName_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_declName_323_);
lean_dec_ref_known(v___x_322_, 2);
v___x_324_ = lean_st_ref_get(v_a_320_);
v_env_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_ref(v_env_325_);
lean_dec(v___x_324_);
v___x_326_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_325_, v_declName_323_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_e_316_);
v___x_327_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
else
{
uint8_t v___x_329_; lean_object* v___x_330_; 
v___x_329_ = 0;
v___x_330_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_316_, v___x_329_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_350_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_350_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_345_; 
v_val_335_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_345_ == 0)
{
v___x_337_ = v_a_331_;
v_isShared_338_ = v_isSharedCheck_345_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v_a_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_345_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_val_335_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_342_ = v___x_333_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec(v_a_331_);
v___x_346_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_346_);
v___x_348_ = v___x_333_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_330_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_330_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v___x_322_);
lean_dec_ref(v_e_316_);
v___x_359_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_367_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_368_, lean_object* v_e_369_){
_start:
{
if (lean_obj_tag(v_e_369_) == 4)
{
lean_object* v_declName_370_; uint8_t v___x_371_; 
v_declName_370_ = lean_ctor_get(v_e_369_, 0);
lean_inc(v_declName_370_);
lean_dec_ref_known(v_e_369_, 2);
v___x_371_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_368_, v_declName_370_);
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
lean_dec_ref(v_e_369_);
lean_dec_ref(v_env_368_);
v___x_372_ = 0;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_373_, lean_object* v_e_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_373_, v_e_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; lean_object* v_env_381_; lean_object* v___f_382_; lean_object* v___x_383_; 
v___x_380_ = lean_st_ref_get(v_a_378_);
v_env_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_381_);
lean_dec(v___x_380_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_382_, 0, v_env_381_);
v___x_383_ = lean_find_expr(v___f_382_, v_e_377_);
lean_dec_ref(v___f_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = 0;
v___x_385_ = lean_box(v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_395_; 
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_396_);
v___x_388_ = v___x_383_;
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
else
{
lean_dec(v___x_383_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = 1;
v___x_391_ = lean_box(v___x_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_e_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_401_, v_a_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_e_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_e_411_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_426_, lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_apply_1(v_x_427_, lean_box(0));
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_435_, lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_435_, v_x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
else
{
lean_object* v_key_446_; lean_object* v_tail_447_; uint8_t v___x_448_; 
v_key_446_ = lean_ctor_get(v_x_444_, 0);
v_tail_447_ = lean_ctor_get(v_x_444_, 2);
v___x_448_ = l_Lean_ExprStructEq_beq(v_key_446_, v_a_443_);
if (v___x_448_ == 0)
{
v_x_444_ = v_tail_447_;
goto _start;
}
else
{
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_450_, v_x_451_);
lean_dec(v_x_451_);
lean_dec_ref(v_a_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
return v_x_454_;
}
else
{
lean_object* v_key_456_; lean_object* v_value_457_; lean_object* v_tail_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_481_; 
v_key_456_ = lean_ctor_get(v_x_455_, 0);
v_value_457_ = lean_ctor_get(v_x_455_, 1);
v_tail_458_ = lean_ctor_get(v_x_455_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_481_ == 0)
{
v___x_460_ = v_x_455_;
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_tail_458_);
lean_inc(v_value_457_);
lean_inc(v_key_456_);
lean_dec(v_x_455_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v_fold_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_462_ = lean_array_get_size(v_x_454_);
v___x_463_ = l_Lean_ExprStructEq_hash(v_key_456_);
v___x_464_ = 32ULL;
v___x_465_ = lean_uint64_shift_right(v___x_463_, v___x_464_);
v_fold_466_ = lean_uint64_xor(v___x_463_, v___x_465_);
v___x_467_ = 16ULL;
v___x_468_ = lean_uint64_shift_right(v_fold_466_, v___x_467_);
v___x_469_ = lean_uint64_xor(v_fold_466_, v___x_468_);
v___x_470_ = lean_uint64_to_usize(v___x_469_);
v___x_471_ = lean_usize_of_nat(v___x_462_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_sub(v___x_471_, v___x_472_);
v___x_474_ = lean_usize_land(v___x_470_, v___x_473_);
v___x_475_ = lean_array_uget_borrowed(v_x_454_, v___x_474_);
lean_inc(v___x_475_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 2, v___x_475_);
v___x_477_ = v___x_460_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_key_456_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_value_457_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_array_uset(v_x_454_, v___x_474_, v___x_477_);
v_x_454_ = v___x_478_;
v_x_455_ = v_tail_458_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_482_, lean_object* v_source_483_, lean_object* v_target_484_){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_array_get_size(v_source_483_);
v___x_486_ = lean_nat_dec_lt(v_i_482_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec_ref(v_source_483_);
lean_dec(v_i_482_);
return v_target_484_;
}
else
{
lean_object* v_es_487_; lean_object* v___x_488_; lean_object* v_source_489_; lean_object* v_target_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_es_487_ = lean_array_fget(v_source_483_, v_i_482_);
v___x_488_ = lean_box(0);
v_source_489_ = lean_array_fset(v_source_483_, v_i_482_, v___x_488_);
v_target_490_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_484_, v_es_487_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_i_482_, v___x_491_);
lean_dec(v_i_482_);
v_i_482_ = v___x_492_;
v_source_483_ = v_source_489_;
v_target_484_ = v_target_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_nbuckets_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_495_ = lean_array_get_size(v_data_494_);
v___x_496_ = lean_unsigned_to_nat(2u);
v_nbuckets_497_ = lean_nat_mul(v___x_495_, v___x_496_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_box(0);
v___x_500_ = lean_mk_array(v_nbuckets_497_, v___x_499_);
v___x_501_ = lean_array_propagate_mark(v_data_494_, v___x_500_);
v___x_502_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_498_, v_data_494_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_503_, lean_object* v_b_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_dec(v_b_504_);
lean_dec_ref(v_a_503_);
return v_x_505_;
}
else
{
lean_object* v_key_506_; lean_object* v_value_507_; lean_object* v_tail_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_520_; 
v_key_506_ = lean_ctor_get(v_x_505_, 0);
v_value_507_ = lean_ctor_get(v_x_505_, 1);
v_tail_508_ = lean_ctor_get(v_x_505_, 2);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_520_ == 0)
{
v___x_510_ = v_x_505_;
v_isShared_511_ = v_isSharedCheck_520_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_tail_508_);
lean_inc(v_value_507_);
lean_inc(v_key_506_);
lean_dec(v_x_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_520_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_ExprStructEq_beq(v_key_506_, v_a_503_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_503_, v_b_504_, v_tail_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 2, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_key_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_value_507_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_value_507_);
lean_dec(v_key_506_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v_b_504_);
lean_ctor_set(v___x_510_, 0, v_a_503_);
v___x_518_ = v___x_510_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_503_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_b_504_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_tail_508_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_521_, lean_object* v_a_522_, lean_object* v_b_523_){
_start:
{
lean_object* v_size_524_; lean_object* v_buckets_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_568_; 
v_size_524_ = lean_ctor_get(v_m_521_, 0);
v_buckets_525_ = lean_ctor_get(v_m_521_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_m_521_);
if (v_isSharedCheck_568_ == 0)
{
v___x_527_ = v_m_521_;
v_isShared_528_ = v_isSharedCheck_568_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_buckets_525_);
lean_inc(v_size_524_);
lean_dec(v_m_521_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_568_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; uint64_t v___x_530_; uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v_fold_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v_bkt_542_; uint8_t v___x_543_; 
v___x_529_ = lean_array_get_size(v_buckets_525_);
v___x_530_ = l_Lean_ExprStructEq_hash(v_a_522_);
v___x_531_ = 32ULL;
v___x_532_ = lean_uint64_shift_right(v___x_530_, v___x_531_);
v_fold_533_ = lean_uint64_xor(v___x_530_, v___x_532_);
v___x_534_ = 16ULL;
v___x_535_ = lean_uint64_shift_right(v_fold_533_, v___x_534_);
v___x_536_ = lean_uint64_xor(v_fold_533_, v___x_535_);
v___x_537_ = lean_uint64_to_usize(v___x_536_);
v___x_538_ = lean_usize_of_nat(v___x_529_);
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_sub(v___x_538_, v___x_539_);
v___x_541_ = lean_usize_land(v___x_537_, v___x_540_);
v_bkt_542_ = lean_array_uget_borrowed(v_buckets_525_, v___x_541_);
v___x_543_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_522_, v_bkt_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v_size_x27_545_; lean_object* v___x_546_; lean_object* v_buckets_x27_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v_size_x27_545_ = lean_nat_add(v_size_524_, v___x_544_);
lean_dec(v_size_524_);
lean_inc(v_bkt_542_);
v___x_546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_546_, 0, v_a_522_);
lean_ctor_set(v___x_546_, 1, v_b_523_);
lean_ctor_set(v___x_546_, 2, v_bkt_542_);
v_buckets_x27_547_ = lean_array_uset(v_buckets_525_, v___x_541_, v___x_546_);
v___x_548_ = lean_unsigned_to_nat(4u);
v___x_549_ = lean_nat_mul(v_size_x27_545_, v___x_548_);
v___x_550_ = lean_unsigned_to_nat(3u);
v___x_551_ = lean_nat_div(v___x_549_, v___x_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_array_get_size(v_buckets_x27_547_);
v___x_553_ = lean_nat_dec_le(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v_val_554_; lean_object* v___x_556_; 
v_val_554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_547_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v_val_554_);
lean_ctor_set(v___x_527_, 0, v_size_x27_545_);
v___x_556_ = v___x_527_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_size_x27_545_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_val_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v___x_559_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v_buckets_x27_547_);
lean_ctor_set(v___x_527_, 0, v_size_x27_545_);
v___x_559_ = v___x_527_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_size_x27_545_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_buckets_x27_547_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v___x_561_; lean_object* v_buckets_x27_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
lean_inc(v_bkt_542_);
v___x_561_ = lean_box(0);
v_buckets_x27_562_ = lean_array_uset(v_buckets_525_, v___x_541_, v___x_561_);
v___x_563_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_522_, v_b_523_, v_bkt_542_);
v___x_564_ = lean_array_uset(v_buckets_x27_562_, v___x_541_, v___x_563_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_564_);
v___x_566_ = v___x_527_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_size_524_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_569_, lean_object* v_e_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_st_ref_take(v_a_569_);
v___x_574_ = lean_box(0);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_573_, v_e_570_, v_a_571_);
v___x_576_ = lean_st_ref_put(v_a_569_, v___x_575_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_577_, lean_object* v_e_578_, lean_object* v_a_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_577_, v_e_578_, v_a_579_);
lean_dec(v_a_577_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_maxRecDepthErrorMessage;
v___x_588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_590_ = l_Lean_MessageData_ofFormat(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_592_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_593_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_ref_594_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___y_610_; lean_object* v_toCold_619_; lean_object* v_currRecDepth_620_; lean_object* v_ref_621_; uint16_t v_optionFlags_622_; uint8_t v_suppressElabErrors_623_; uint8_t v_checkDeprecated_624_; uint8_t v_isRecordingDeps_625_; lean_object* v_maxRecDepth_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_toCold_619_ = lean_ctor_get(v___y_606_, 0);
v_currRecDepth_620_ = lean_ctor_get(v___y_606_, 1);
v_ref_621_ = lean_ctor_get(v___y_606_, 2);
v_optionFlags_622_ = lean_ctor_get_uint16(v___y_606_, sizeof(void*)*3);
v_suppressElabErrors_623_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*3 + 2);
v_checkDeprecated_624_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*3 + 3);
v_isRecordingDeps_625_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*3 + 4);
v_maxRecDepth_631_ = lean_ctor_get(v_toCold_619_, 3);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_dec_eq(v_maxRecDepth_631_, v___x_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_eq(v_currRecDepth_620_, v_maxRecDepth_631_);
if (v___x_634_ == 0)
{
goto v___jp_626_;
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_x_602_);
lean_inc(v_ref_621_);
v___x_635_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_621_);
v___y_610_ = v___x_635_;
goto v___jp_609_;
}
}
else
{
goto v___jp_626_;
}
v___jp_609_:
{
if (lean_obj_tag(v___y_610_) == 0)
{
return v___y_610_;
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_a_611_ = lean_ctor_get(v___y_610_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___y_610_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___y_610_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___y_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
v___jp_626_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_currRecDepth_620_, v___x_627_);
lean_inc(v_ref_621_);
lean_inc_ref(v_toCold_619_);
v___x_629_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_629_, 0, v_toCold_619_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
lean_ctor_set(v___x_629_, 2, v_ref_621_);
lean_ctor_set_uint16(v___x_629_, sizeof(void*)*3, v_optionFlags_622_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3 + 2, v_suppressElabErrors_623_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3 + 3, v_checkDeprecated_624_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3 + 4, v_isRecordingDeps_625_);
lean_inc(v___y_607_);
lean_inc(v___y_605_);
lean_inc_ref(v___y_604_);
lean_inc(v___y_603_);
v___x_630_ = lean_apply_6(v_x_602_, v___y_603_, v___y_604_, v___y_605_, v___x_629_, v___y_607_, lean_box(0));
v___y_610_ = v___x_630_;
goto v___jp_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_644_, lean_object* v_x_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_apply_1(v_x_645_, lean_box(0));
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_box(0);
return v___x_663_;
}
else
{
lean_object* v_key_664_; lean_object* v_value_665_; lean_object* v_tail_666_; uint8_t v___x_667_; 
v_key_664_ = lean_ctor_get(v_x_662_, 0);
v_value_665_ = lean_ctor_get(v_x_662_, 1);
v_tail_666_ = lean_ctor_get(v_x_662_, 2);
v___x_667_ = l_Lean_ExprStructEq_beq(v_key_664_, v_a_661_);
if (v___x_667_ == 0)
{
v_x_662_ = v_tail_666_;
goto _start;
}
else
{
lean_object* v___x_669_; 
lean_inc(v_value_665_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_value_665_);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_670_, v_x_671_);
lean_dec(v_x_671_);
lean_dec_ref(v_a_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_buckets_675_; lean_object* v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v_fold_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_buckets_675_ = lean_ctor_get(v_m_673_, 1);
v___x_676_ = lean_array_get_size(v_buckets_675_);
v___x_677_ = l_Lean_ExprStructEq_hash(v_a_674_);
v___x_678_ = 32ULL;
v___x_679_ = lean_uint64_shift_right(v___x_677_, v___x_678_);
v_fold_680_ = lean_uint64_xor(v___x_677_, v___x_679_);
v___x_681_ = 16ULL;
v___x_682_ = lean_uint64_shift_right(v_fold_680_, v___x_681_);
v___x_683_ = lean_uint64_xor(v_fold_680_, v___x_682_);
v___x_684_ = lean_uint64_to_usize(v___x_683_);
v___x_685_ = lean_usize_of_nat(v___x_676_);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_sub(v___x_685_, v___x_686_);
v___x_688_ = lean_usize_land(v___x_684_, v___x_687_);
v___x_689_ = lean_array_uget_borrowed(v_buckets_675_, v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_674_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_691_, v_a_692_);
lean_dec_ref(v_a_692_);
lean_dec_ref(v_m_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_694_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_708_, lean_object* v___y_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_709_);
v___x_716_ = lean_apply_7(v_k_708_, v_b_710_, v___y_709_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_717_, lean_object* v___y_718_, lean_object* v_b_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_717_, v___y_718_, v_b_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_718_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_726_, uint8_t v_bi_727_, lean_object* v_type_728_, lean_object* v_k_729_, uint8_t v_kind_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___f_737_; lean_object* v___x_738_; 
lean_inc(v___y_731_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_737_, 0, v_k_729_);
lean_closure_set(v___f_737_, 1, v___y_731_);
v___x_738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_726_, v_bi_727_, v_type_728_, v___f_737_, v_kind_730_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_738_) == 0)
{
return v___x_738_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_747_, lean_object* v_bi_748_, lean_object* v_type_749_, lean_object* v_k_750_, lean_object* v_kind_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v_bi_boxed_758_; uint8_t v_kind_boxed_759_; lean_object* v_res_760_; 
v_bi_boxed_758_ = lean_unbox(v_bi_748_);
v_kind_boxed_759_ = lean_unbox(v_kind_751_);
v_res_760_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_747_, v_bi_boxed_758_, v_type_749_, v_k_750_, v_kind_boxed_759_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_761_, lean_object* v_type_762_, lean_object* v_val_763_, lean_object* v_k_764_, uint8_t v_nondep_765_, uint8_t v_kind_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; 
lean_inc(v___y_767_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_773_, 0, v_k_764_);
lean_closure_set(v___f_773_, 1, v___y_767_);
v___x_774_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_761_, v_type_762_, v_val_763_, v___f_773_, v_nondep_765_, v_kind_766_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
return v___x_774_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_783_, lean_object* v_type_784_, lean_object* v_val_785_, lean_object* v_k_786_, lean_object* v_nondep_787_, lean_object* v_kind_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v_nondep_boxed_795_; uint8_t v_kind_boxed_796_; lean_object* v_res_797_; 
v_nondep_boxed_795_ = lean_unbox(v_nondep_787_);
v_kind_boxed_796_ = lean_unbox(v_kind_788_);
v_res_797_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_783_, v_type_784_, v_val_785_, v_k_786_, v_nondep_boxed_795_, v_kind_boxed_796_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_798_, lean_object* v_pre_799_, lean_object* v_post_800_, lean_object* v_usedLetOnly_801_, lean_object* v_skipConstInApp_802_, lean_object* v_skipInstances_803_, lean_object* v_body_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v_usedLetOnly_boxed_812_; uint8_t v_skipConstInApp_boxed_813_; uint8_t v_skipInstances_boxed_814_; lean_object* v_res_815_; 
v_usedLetOnly_boxed_812_ = lean_unbox(v_usedLetOnly_801_);
v_skipConstInApp_boxed_813_ = lean_unbox(v_skipConstInApp_802_);
v_skipInstances_boxed_814_ = lean_unbox(v_skipInstances_803_);
v_res_815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_798_, v_pre_799_, v_post_800_, v_usedLetOnly_boxed_812_, v_skipConstInApp_boxed_813_, v_skipInstances_boxed_814_, v_body_804_, v_x_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_819_, lean_object* v_pre_820_, lean_object* v_post_821_, uint8_t v_usedLetOnly_822_, uint8_t v_skipConstInApp_823_, uint8_t v_skipInstances_824_, lean_object* v_body_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_array_push(v_fvars_819_, v_x_826_);
v___x_834_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_820_, v_post_821_, v_usedLetOnly_822_, v_skipConstInApp_823_, v_skipInstances_824_, v___x_833_, v_body_825_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_835_, lean_object* v_pre_836_, lean_object* v_post_837_, lean_object* v_usedLetOnly_838_, lean_object* v_skipConstInApp_839_, lean_object* v_skipInstances_840_, lean_object* v_body_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v_usedLetOnly_boxed_849_; uint8_t v_skipConstInApp_boxed_850_; uint8_t v_skipInstances_boxed_851_; lean_object* v_res_852_; 
v_usedLetOnly_boxed_849_ = lean_unbox(v_usedLetOnly_838_);
v_skipConstInApp_boxed_850_ = lean_unbox(v_skipConstInApp_839_);
v_skipInstances_boxed_851_ = lean_unbox(v_skipInstances_840_);
v_res_852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_835_, v_pre_836_, v_post_837_, v_usedLetOnly_boxed_849_, v_skipConstInApp_boxed_850_, v_skipInstances_boxed_851_, v_body_841_, v_x_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_853_, lean_object* v_post_854_, uint8_t v_usedLetOnly_855_, uint8_t v_skipConstInApp_856_, uint8_t v_skipInstances_857_, lean_object* v_e_858_, lean_object* v_a_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; 
lean_inc_ref(v_post_854_);
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc_ref(v_e_858_);
v___x_865_ = lean_apply_6(v_post_854_, v_e_858_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, lean_box(0));
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_884_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_884_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_884_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_884_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
switch(lean_obj_tag(v_a_866_))
{
case 0:
{
lean_object* v_e_870_; lean_object* v___x_872_; 
lean_dec_ref(v_e_858_);
lean_dec_ref(v_post_854_);
lean_dec_ref(v_pre_853_);
v_e_870_ = lean_ctor_get(v_a_866_, 0);
lean_inc_ref(v_e_870_);
lean_dec_ref_known(v_a_866_, 1);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_e_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_e_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
case 1:
{
lean_object* v_e_874_; lean_object* v___x_875_; 
lean_del_object(v___x_868_);
lean_dec_ref(v_e_858_);
v_e_874_ = lean_ctor_get(v_a_866_, 0);
lean_inc_ref(v_e_874_);
lean_dec_ref_known(v_a_866_, 1);
v___x_875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_853_, v_post_854_, v_usedLetOnly_855_, v_skipConstInApp_856_, v_skipInstances_857_, v_e_874_, v_a_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_875_;
}
default: 
{
lean_object* v_e_x3f_876_; 
lean_dec_ref(v_post_854_);
lean_dec_ref(v_pre_853_);
v_e_x3f_876_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_e_x3f_876_);
lean_dec_ref_known(v_a_866_, 1);
if (lean_obj_tag(v_e_x3f_876_) == 0)
{
lean_object* v___x_878_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_e_858_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_e_858_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v_val_880_; lean_object* v___x_882_; 
lean_dec_ref(v_e_858_);
v_val_880_ = lean_ctor_get(v_e_x3f_876_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_e_x3f_876_, 1);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_val_880_);
v___x_882_ = v___x_868_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_val_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v_e_858_);
lean_dec_ref(v_post_854_);
lean_dec_ref(v_pre_853_);
v_a_885_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_865_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_865_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_893_, lean_object* v_post_894_, uint8_t v_usedLetOnly_895_, uint8_t v_skipConstInApp_896_, uint8_t v_skipInstances_897_, lean_object* v_fvars_898_, lean_object* v_e_899_, lean_object* v_a_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
if (lean_obj_tag(v_e_899_) == 6)
{
lean_object* v_binderName_906_; lean_object* v_binderType_907_; lean_object* v_body_908_; uint8_t v_binderInfo_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_binderName_906_ = lean_ctor_get(v_e_899_, 0);
lean_inc(v_binderName_906_);
v_binderType_907_ = lean_ctor_get(v_e_899_, 1);
lean_inc_ref(v_binderType_907_);
v_body_908_ = lean_ctor_get(v_e_899_, 2);
lean_inc_ref(v_body_908_);
v_binderInfo_909_ = lean_ctor_get_uint8(v_e_899_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_899_, 3);
v___x_910_ = lean_box(v_usedLetOnly_895_);
v___x_911_ = lean_box(v_skipConstInApp_896_);
v___x_912_ = lean_box(v_skipInstances_897_);
lean_inc_ref(v_post_894_);
lean_inc_ref(v_pre_893_);
lean_inc_ref(v_fvars_898_);
v___f_913_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_913_, 0, v_fvars_898_);
lean_closure_set(v___f_913_, 1, v_pre_893_);
lean_closure_set(v___f_913_, 2, v_post_894_);
lean_closure_set(v___f_913_, 3, v___x_910_);
lean_closure_set(v___f_913_, 4, v___x_911_);
lean_closure_set(v___f_913_, 5, v___x_912_);
lean_closure_set(v___f_913_, 6, v_body_908_);
v___x_914_ = lean_expr_instantiate_rev(v_binderType_907_, v_fvars_898_);
lean_dec_ref(v_fvars_898_);
lean_dec_ref(v_binderType_907_);
v___x_915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_893_, v_post_894_, v_usedLetOnly_895_, v_skipConstInApp_896_, v_skipInstances_897_, v___x_914_, v_a_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; uint8_t v___x_917_; lean_object* v___x_918_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = 0;
v___x_918_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_906_, v_binderInfo_909_, v_a_916_, v___f_913_, v___x_917_, v_a_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_918_;
}
else
{
lean_dec_ref(v___f_913_);
lean_dec(v_binderName_906_);
return v___x_915_;
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_expr_instantiate_rev(v_e_899_, v_fvars_898_);
lean_dec_ref(v_e_899_);
lean_inc_ref(v_post_894_);
lean_inc_ref(v_pre_893_);
v___x_920_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_893_, v_post_894_, v_usedLetOnly_895_, v_skipConstInApp_896_, v_skipInstances_897_, v___x_919_, v_a_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; uint8_t v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = 0;
v___x_923_ = 1;
v___x_924_ = 1;
v___x_925_ = l_Lean_Meta_mkLambdaFVars(v_fvars_898_, v_a_921_, v___x_922_, v_usedLetOnly_895_, v___x_922_, v___x_923_, v___x_924_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec_ref(v_fvars_898_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_893_, v_post_894_, v_usedLetOnly_895_, v_skipConstInApp_896_, v_skipInstances_897_, v_a_926_, v_a_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_927_;
}
else
{
lean_dec_ref(v_post_894_);
lean_dec_ref(v_pre_893_);
return v___x_925_;
}
}
else
{
lean_dec_ref(v_fvars_898_);
lean_dec_ref(v_post_894_);
lean_dec_ref(v_pre_893_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_928_, lean_object* v_pre_929_, lean_object* v_post_930_, uint8_t v_usedLetOnly_931_, uint8_t v_skipConstInApp_932_, uint8_t v_skipInstances_933_, lean_object* v_body_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_array_push(v_fvars_928_, v_x_935_);
v___x_943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_929_, v_post_930_, v_usedLetOnly_931_, v_skipConstInApp_932_, v_skipInstances_933_, v___x_942_, v_body_934_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_944_, lean_object* v_pre_945_, lean_object* v_post_946_, lean_object* v_usedLetOnly_947_, lean_object* v_skipConstInApp_948_, lean_object* v_skipInstances_949_, lean_object* v_body_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v_usedLetOnly_boxed_958_; uint8_t v_skipConstInApp_boxed_959_; uint8_t v_skipInstances_boxed_960_; lean_object* v_res_961_; 
v_usedLetOnly_boxed_958_ = lean_unbox(v_usedLetOnly_947_);
v_skipConstInApp_boxed_959_ = lean_unbox(v_skipConstInApp_948_);
v_skipInstances_boxed_960_ = lean_unbox(v_skipInstances_949_);
v_res_961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_944_, v_pre_945_, v_post_946_, v_usedLetOnly_boxed_958_, v_skipConstInApp_boxed_959_, v_skipInstances_boxed_960_, v_body_950_, v_x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_962_, lean_object* v_post_963_, uint8_t v_usedLetOnly_964_, uint8_t v_skipConstInApp_965_, uint8_t v_skipInstances_966_, lean_object* v_fvars_967_, lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
if (lean_obj_tag(v_e_968_) == 8)
{
lean_object* v_declName_975_; lean_object* v_type_976_; lean_object* v_value_977_; lean_object* v_body_978_; uint8_t v_nondep_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_declName_975_ = lean_ctor_get(v_e_968_, 0);
lean_inc(v_declName_975_);
v_type_976_ = lean_ctor_get(v_e_968_, 1);
lean_inc_ref(v_type_976_);
v_value_977_ = lean_ctor_get(v_e_968_, 2);
lean_inc_ref(v_value_977_);
v_body_978_ = lean_ctor_get(v_e_968_, 3);
lean_inc_ref(v_body_978_);
v_nondep_979_ = lean_ctor_get_uint8(v_e_968_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_968_, 4);
v___x_980_ = lean_box(v_usedLetOnly_964_);
v___x_981_ = lean_box(v_skipConstInApp_965_);
v___x_982_ = lean_box(v_skipInstances_966_);
lean_inc_ref_n(v_post_963_, 2);
lean_inc_ref_n(v_pre_962_, 2);
lean_inc_ref(v_fvars_967_);
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_983_, 0, v_fvars_967_);
lean_closure_set(v___f_983_, 1, v_pre_962_);
lean_closure_set(v___f_983_, 2, v_post_963_);
lean_closure_set(v___f_983_, 3, v___x_980_);
lean_closure_set(v___f_983_, 4, v___x_981_);
lean_closure_set(v___f_983_, 5, v___x_982_);
lean_closure_set(v___f_983_, 6, v_body_978_);
v___x_984_ = lean_expr_instantiate_rev(v_type_976_, v_fvars_967_);
lean_dec_ref(v_type_976_);
v___x_985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_962_, v_post_963_, v_usedLetOnly_964_, v_skipConstInApp_965_, v_skipInstances_966_, v___x_984_, v_a_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = lean_expr_instantiate_rev(v_value_977_, v_fvars_967_);
lean_dec_ref(v_fvars_967_);
lean_dec_ref(v_value_977_);
v___x_988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_962_, v_post_963_, v_usedLetOnly_964_, v_skipConstInApp_965_, v_skipInstances_966_, v___x_987_, v_a_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; uint8_t v___x_990_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = 0;
v___x_991_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_975_, v_a_986_, v_a_989_, v___f_983_, v_nondep_979_, v___x_990_, v_a_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_991_;
}
else
{
lean_dec(v_a_986_);
lean_dec_ref(v___f_983_);
lean_dec(v_declName_975_);
return v___x_988_;
}
}
else
{
lean_dec_ref(v___f_983_);
lean_dec_ref(v_value_977_);
lean_dec(v_declName_975_);
lean_dec_ref(v_fvars_967_);
lean_dec_ref(v_post_963_);
lean_dec_ref(v_pre_962_);
return v___x_985_;
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_expr_instantiate_rev(v_e_968_, v_fvars_967_);
lean_dec_ref(v_e_968_);
lean_inc_ref(v_post_963_);
lean_inc_ref(v_pre_962_);
v___x_993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_962_, v_post_963_, v_usedLetOnly_964_, v_skipConstInApp_965_, v_skipInstances_966_, v___x_992_, v_a_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; uint8_t v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = 0;
v___x_996_ = 1;
v___x_997_ = l_Lean_Meta_mkLetFVars(v_fvars_967_, v_a_994_, v_usedLetOnly_964_, v___x_995_, v___x_996_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec_ref(v_fvars_967_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_962_, v_post_963_, v_usedLetOnly_964_, v_skipConstInApp_965_, v_skipInstances_966_, v_a_998_, v_a_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_999_;
}
else
{
lean_dec_ref(v_post_963_);
lean_dec_ref(v_pre_962_);
return v___x_997_;
}
}
else
{
lean_dec_ref(v_fvars_967_);
lean_dec_ref(v_post_963_);
lean_dec_ref(v_pre_962_);
return v___x_993_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1000_; lean_object* v_dummy_1001_; 
v___x_1000_ = lean_box(0);
v_dummy_1001_ = l_Lean_Expr_sort___override(v___x_1000_);
return v_dummy_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_1002_, lean_object* v_post_1003_, uint8_t v_usedLetOnly_1004_, uint8_t v_skipConstInApp_1005_, uint8_t v_skipInstances_1006_, size_t v_sz_1007_, size_t v_i_1008_, lean_object* v_bs_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_lt(v_i_1008_, v_sz_1007_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref(v_post_1003_);
lean_dec_ref(v_pre_1002_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_bs_1009_);
return v___x_1017_;
}
else
{
lean_object* v_v_1018_; lean_object* v___x_1019_; lean_object* v_bs_x27_1020_; lean_object* v___x_1021_; 
v_v_1018_ = lean_array_uget(v_bs_1009_, v_i_1008_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v_bs_x27_1020_ = lean_array_uset(v_bs_1009_, v_i_1008_, v___x_1019_);
lean_inc_ref(v_post_1003_);
lean_inc_ref(v_pre_1002_);
v___x_1021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1002_, v_post_1003_, v_usedLetOnly_1004_, v_skipConstInApp_1005_, v_skipInstances_1006_, v_v_1018_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1008_, v___x_1023_);
v___x_1025_ = lean_array_uset(v_bs_x27_1020_, v_i_1008_, v_a_1022_);
v_i_1008_ = v___x_1024_;
v_bs_1009_ = v___x_1025_;
goto _start;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_bs_x27_1020_);
lean_dec_ref(v_post_1003_);
lean_dec_ref(v_pre_1002_);
v_a_1027_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1035_, lean_object* v_post_1036_, uint8_t v_usedLetOnly_1037_, uint8_t v_skipConstInApp_1038_, uint8_t v_skipInstances_1039_, lean_object* v___x_1040_, lean_object* v___y_1041_, lean_object* v_b_1042_, lean_object* v_a_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1035_, v_post_1036_, v_usedLetOnly_1037_, v_skipConstInApp_1038_, v_skipInstances_1039_, v___x_1040_, v___y_1041_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1059_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1059_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1059_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = lean_array_fset(v_b_1042_, v_a_1043_, v_a_1050_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v_b_1042_);
v_a_1060_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1049_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1049_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1068_, lean_object* v_post_1069_, lean_object* v_usedLetOnly_1070_, lean_object* v_skipConstInApp_1071_, lean_object* v_skipInstances_1072_, lean_object* v___x_1073_, lean_object* v___y_1074_, lean_object* v_b_1075_, lean_object* v_a_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
uint8_t v_usedLetOnly_boxed_1082_; uint8_t v_skipConstInApp_boxed_1083_; uint8_t v_skipInstances_boxed_1084_; lean_object* v_res_1085_; 
v_usedLetOnly_boxed_1082_ = lean_unbox(v_usedLetOnly_1070_);
v_skipConstInApp_boxed_1083_ = lean_unbox(v_skipConstInApp_1071_);
v_skipInstances_boxed_1084_ = lean_unbox(v_skipInstances_1072_);
v_res_1085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1068_, v_post_1069_, v_usedLetOnly_boxed_1082_, v_skipConstInApp_boxed_1083_, v_skipInstances_boxed_1084_, v___x_1073_, v___y_1074_, v_b_1075_, v_a_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_a_1076_);
lean_dec(v___y_1074_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1086_, lean_object* v___x_1087_, lean_object* v_pre_1088_, lean_object* v_post_1089_, uint8_t v_usedLetOnly_1090_, uint8_t v_skipConstInApp_1091_, uint8_t v_skipInstances_1092_, lean_object* v_a_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___y_1102_; uint8_t v___x_1125_; 
v___x_1125_ = lean_nat_dec_lt(v_a_1093_, v_upperBound_1086_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec(v_a_1093_);
lean_dec_ref(v_post_1089_);
lean_dec_ref(v_pre_1088_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_b_1094_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_array_fget_borrowed(v_b_1094_, v_a_1093_);
v___x_1128_ = lean_array_get_size(v___x_1087_);
v___x_1129_ = lean_nat_dec_lt(v_a_1093_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; 
lean_inc(v___x_1127_);
v___x_1130_ = lean_box(v_usedLetOnly_1090_);
v___x_1131_ = lean_box(v_skipConstInApp_1091_);
v___x_1132_ = lean_box(v_skipInstances_1092_);
lean_inc(v_a_1093_);
lean_inc(v___y_1095_);
lean_inc_ref(v_post_1089_);
lean_inc_ref(v_pre_1088_);
v___f_1133_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1133_, 0, v_pre_1088_);
lean_closure_set(v___f_1133_, 1, v_post_1089_);
lean_closure_set(v___f_1133_, 2, v___x_1130_);
lean_closure_set(v___f_1133_, 3, v___x_1131_);
lean_closure_set(v___f_1133_, 4, v___x_1132_);
lean_closure_set(v___f_1133_, 5, v___x_1127_);
lean_closure_set(v___f_1133_, 6, v___y_1095_);
lean_closure_set(v___f_1133_, 7, v_b_1094_);
lean_closure_set(v___f_1133_, 8, v_a_1093_);
v___y_1102_ = v___f_1133_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1134_; uint8_t v_isInstance_1135_; 
v___x_1134_ = lean_array_fget_borrowed(v___x_1087_, v_a_1093_);
v_isInstance_1135_ = lean_ctor_get_uint8(v___x_1134_, sizeof(void*)*1 + 4);
if (v_isInstance_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; 
lean_inc(v___x_1127_);
v___x_1136_ = lean_box(v_usedLetOnly_1090_);
v___x_1137_ = lean_box(v_skipConstInApp_1091_);
v___x_1138_ = lean_box(v_skipInstances_1092_);
lean_inc(v_a_1093_);
lean_inc(v___y_1095_);
lean_inc_ref(v_post_1089_);
lean_inc_ref(v_pre_1088_);
v___f_1139_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1139_, 0, v_pre_1088_);
lean_closure_set(v___f_1139_, 1, v_post_1089_);
lean_closure_set(v___f_1139_, 2, v___x_1136_);
lean_closure_set(v___f_1139_, 3, v___x_1137_);
lean_closure_set(v___f_1139_, 4, v___x_1138_);
lean_closure_set(v___f_1139_, 5, v___x_1127_);
lean_closure_set(v___f_1139_, 6, v___y_1095_);
lean_closure_set(v___f_1139_, 7, v_b_1094_);
lean_closure_set(v___f_1139_, 8, v_a_1093_);
v___y_1102_ = v___f_1139_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1140_; lean_object* v___f_1141_; 
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_b_1094_);
v___f_1141_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1141_, 0, v___x_1140_);
v___y_1102_ = v___f_1141_;
goto v___jp_1101_;
}
}
}
v___jp_1101_:
{
lean_object* v___x_1103_; 
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
v___x_1103_ = lean_apply_5(v___y_1102_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1116_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1116_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1116_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
if (lean_obj_tag(v_a_1104_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; 
lean_dec(v_a_1093_);
lean_dec_ref(v_post_1089_);
lean_dec_ref(v_pre_1088_);
v_a_1108_ = lean_ctor_get(v_a_1104_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v_a_1104_, 1);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v_a_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_del_object(v___x_1106_);
v_a_1112_ = lean_ctor_get(v_a_1104_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v_a_1104_, 1);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_a_1093_, v___x_1113_);
lean_dec(v_a_1093_);
v_a_1093_ = v___x_1114_;
v_b_1094_ = v_a_1112_;
goto _start;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_a_1093_);
lean_dec_ref(v_post_1089_);
lean_dec_ref(v_pre_1088_);
v_a_1117_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1103_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1103_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1142_, lean_object* v_pre_1143_, lean_object* v_post_1144_, uint8_t v_usedLetOnly_1145_, uint8_t v_skipConstInApp_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_f_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; 
if (lean_obj_tag(v_x_1147_) == 5)
{
lean_object* v_fn_1205_; lean_object* v_arg_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_fn_1205_ = lean_ctor_get(v_x_1147_, 0);
lean_inc_ref(v_fn_1205_);
v_arg_1206_ = lean_ctor_get(v_x_1147_, 1);
lean_inc_ref(v_arg_1206_);
lean_dec_ref_known(v_x_1147_, 2);
v___x_1207_ = lean_array_set(v_x_1148_, v_x_1149_, v_arg_1206_);
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_sub(v_x_1149_, v___x_1208_);
lean_dec(v_x_1149_);
v_x_1147_ = v_fn_1205_;
v_x_1148_ = v___x_1207_;
v_x_1149_ = v___x_1209_;
goto _start;
}
else
{
lean_dec(v_x_1149_);
if (v_skipConstInApp_1146_ == 0)
{
goto v___jp_1202_;
}
else
{
uint8_t v___x_1211_; 
v___x_1211_ = l_Lean_Expr_isConst(v_x_1147_);
if (v___x_1211_ == 0)
{
goto v___jp_1202_;
}
else
{
v_f_1157_ = v_x_1147_;
v___y_1158_ = v___y_1150_;
v___y_1159_ = v___y_1151_;
v___y_1160_ = v___y_1152_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___y_1154_;
goto v___jp_1156_;
}
}
}
v___jp_1156_:
{
if (v_skipInstances_1142_ == 0)
{
size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_sz_1163_ = lean_array_size(v_x_1148_);
v___x_1164_ = ((size_t)0ULL);
lean_inc_ref(v_post_1144_);
lean_inc_ref(v_pre_1143_);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1143_, v_post_1144_, v_usedLetOnly_1145_, v_skipConstInApp_1146_, v_skipInstances_1142_, v_sz_1163_, v___x_1164_, v_x_1148_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = l_Lean_mkAppN(v_f_1157_, v_a_1166_);
lean_dec(v_a_1166_);
v___x_1168_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1143_, v_post_1144_, v_usedLetOnly_1145_, v_skipConstInApp_1146_, v_skipInstances_1142_, v___x_1167_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_f_1157_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
v_a_1169_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1165_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1165_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_array_get_size(v_x_1148_);
lean_inc_ref(v_f_1157_);
v___x_1178_ = l_Lean_Meta_getFunInfoNArgs(v_f_1157_, v___x_1177_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v_paramInfo_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v_paramInfo_1180_ = lean_ctor_get(v_a_1179_, 0);
lean_inc_ref(v_paramInfo_1180_);
lean_dec(v_a_1179_);
v___x_1181_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1144_);
lean_inc_ref(v_pre_1143_);
v___x_1182_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1177_, v_paramInfo_1180_, v_pre_1143_, v_post_1144_, v_usedLetOnly_1145_, v_skipConstInApp_1146_, v_skipInstances_1142_, v___x_1181_, v_x_1148_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec_ref(v_paramInfo_1180_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = l_Lean_mkAppN(v_f_1157_, v_a_1183_);
lean_dec(v_a_1183_);
v___x_1185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1143_, v_post_1144_, v_usedLetOnly_1145_, v_skipConstInApp_1146_, v_skipInstances_1142_, v___x_1184_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1185_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_f_1157_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
v_a_1186_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1182_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_f_1157_);
lean_dec_ref(v_x_1148_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
v_a_1194_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1178_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1178_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
v___jp_1202_:
{
lean_object* v___x_1203_; 
lean_inc_ref(v_post_1144_);
lean_inc_ref(v_pre_1143_);
v___x_1203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1143_, v_post_1144_, v_usedLetOnly_1145_, v_skipConstInApp_1146_, v_skipInstances_1142_, v_x_1147_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v_f_1157_ = v_a_1204_;
v___y_1158_ = v___y_1150_;
v___y_1159_ = v___y_1151_;
v___y_1160_ = v___y_1152_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___y_1154_;
goto v___jp_1156_;
}
else
{
lean_dec_ref(v_x_1148_);
lean_dec_ref(v_post_1144_);
lean_dec_ref(v_pre_1143_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1212_, lean_object* v_pre_1213_, lean_object* v_e_1214_, lean_object* v_post_1215_, uint8_t v_usedLetOnly_1216_, uint8_t v_skipConstInApp_1217_, uint8_t v_skipInstances_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Core_checkSystem(v___x_1212_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1225_, 1);
lean_inc_ref(v_pre_1213_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc_ref(v_e_1214_);
v___x_1226_ = lean_apply_6(v_pre_1213_, v_e_1214_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1275_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1275_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1275_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___y_1232_; 
switch(lean_obj_tag(v_a_1227_))
{
case 0:
{
lean_object* v_e_1267_; lean_object* v___x_1269_; 
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_e_1214_);
lean_dec_ref(v_pre_1213_);
v_e_1267_ = lean_ctor_get(v_a_1227_, 0);
lean_inc_ref(v_e_1267_);
lean_dec_ref_known(v_a_1227_, 1);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v_e_1267_);
v___x_1269_ = v___x_1229_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_e_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
case 1:
{
lean_object* v_e_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1229_);
lean_dec_ref(v_e_1214_);
v_e_1271_ = lean_ctor_get(v_a_1227_, 0);
lean_inc_ref(v_e_1271_);
lean_dec_ref_known(v_a_1227_, 1);
v___x_1272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v_e_1271_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1272_;
}
default: 
{
lean_object* v_e_x3f_1273_; 
lean_del_object(v___x_1229_);
v_e_x3f_1273_ = lean_ctor_get(v_a_1227_, 0);
lean_inc(v_e_x3f_1273_);
lean_dec_ref_known(v_a_1227_, 1);
if (lean_obj_tag(v_e_x3f_1273_) == 0)
{
v___y_1232_ = v_e_1214_;
goto v___jp_1231_;
}
else
{
lean_object* v_val_1274_; 
lean_dec_ref(v_e_1214_);
v_val_1274_ = lean_ctor_get(v_e_x3f_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_e_x3f_1273_, 1);
v___y_1232_ = v_val_1274_;
goto v___jp_1231_;
}
}
}
v___jp_1231_:
{
switch(lean_obj_tag(v___y_1232_))
{
case 7:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___x_1233_, v___y_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1234_;
}
case 6:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___x_1235_, v___y_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1236_;
}
case 8:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___x_1237_, v___y_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1238_;
}
case 5:
{
lean_object* v_dummy_1239_; lean_object* v_nargs_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_dummy_1239_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1240_ = l_Lean_Expr_getAppNumArgs(v___y_1232_);
lean_inc(v_nargs_1240_);
v___x_1241_ = lean_mk_array(v_nargs_1240_, v_dummy_1239_);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_sub(v_nargs_1240_, v___x_1242_);
lean_dec(v_nargs_1240_);
v___x_1244_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1218_, v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v___y_1232_, v___x_1241_, v___x_1243_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1244_;
}
case 10:
{
lean_object* v_data_1245_; lean_object* v_expr_1246_; lean_object* v___x_1247_; 
v_data_1245_ = lean_ctor_get(v___y_1232_, 0);
v_expr_1246_ = lean_ctor_get(v___y_1232_, 1);
lean_inc_ref(v_expr_1246_);
lean_inc_ref(v_post_1215_);
lean_inc_ref(v_pre_1213_);
v___x_1247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v_expr_1246_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; size_t v___x_1249_; size_t v___x_1250_; uint8_t v___x_1251_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = lean_ptr_addr(v_expr_1246_);
v___x_1250_ = lean_ptr_addr(v_a_1248_);
v___x_1251_ = lean_usize_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_inc(v_data_1245_);
lean_dec_ref_known(v___y_1232_, 2);
v___x_1252_ = l_Lean_Expr_mdata___override(v_data_1245_, v_a_1248_);
v___x_1253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___x_1252_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_a_1248_);
v___x_1254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___y_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1254_;
}
}
else
{
lean_dec_ref_known(v___y_1232_, 2);
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_pre_1213_);
return v___x_1247_;
}
}
case 11:
{
lean_object* v_typeName_1255_; lean_object* v_idx_1256_; lean_object* v_struct_1257_; lean_object* v___x_1258_; 
v_typeName_1255_ = lean_ctor_get(v___y_1232_, 0);
v_idx_1256_ = lean_ctor_get(v___y_1232_, 1);
v_struct_1257_ = lean_ctor_get(v___y_1232_, 2);
lean_inc_ref(v_struct_1257_);
lean_inc_ref(v_post_1215_);
lean_inc_ref(v_pre_1213_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v_struct_1257_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; size_t v___x_1260_; size_t v___x_1261_; uint8_t v___x_1262_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = lean_ptr_addr(v_struct_1257_);
v___x_1261_ = lean_ptr_addr(v_a_1259_);
v___x_1262_ = lean_usize_dec_eq(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_inc(v_idx_1256_);
lean_inc(v_typeName_1255_);
lean_dec_ref_known(v___y_1232_, 3);
v___x_1263_ = l_Lean_Expr_proj___override(v_typeName_1255_, v_idx_1256_, v_a_1259_);
v___x_1264_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___x_1263_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
lean_dec(v_a_1259_);
v___x_1265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___y_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1265_;
}
}
else
{
lean_dec_ref_known(v___y_1232_, 3);
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_pre_1213_);
return v___x_1258_;
}
}
default: 
{
lean_object* v___x_1266_; 
v___x_1266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1213_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___y_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1266_;
}
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_e_1214_);
lean_dec_ref(v_pre_1213_);
v_a_1276_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1226_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1226_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_e_1214_);
lean_dec_ref(v_pre_1213_);
v_a_1284_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1225_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1225_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1292_, lean_object* v_pre_1293_, lean_object* v_e_1294_, lean_object* v_post_1295_, lean_object* v_usedLetOnly_1296_, lean_object* v_skipConstInApp_1297_, lean_object* v_skipInstances_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_usedLetOnly_boxed_1305_; uint8_t v_skipConstInApp_boxed_1306_; uint8_t v_skipInstances_boxed_1307_; lean_object* v_res_1308_; 
v_usedLetOnly_boxed_1305_ = lean_unbox(v_usedLetOnly_1296_);
v_skipConstInApp_boxed_1306_ = lean_unbox(v_skipConstInApp_1297_);
v_skipInstances_boxed_1307_ = lean_unbox(v_skipInstances_1298_);
v_res_1308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1292_, v_pre_1293_, v_e_1294_, v_post_1295_, v_usedLetOnly_boxed_1305_, v_skipConstInApp_boxed_1306_, v_skipInstances_boxed_1307_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1309_, lean_object* v_post_1310_, uint8_t v_usedLetOnly_1311_, uint8_t v_skipConstInApp_1312_, uint8_t v_skipInstances_1313_, lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_inc(v_a_1315_);
v___x_1321_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, lean_box(0));
lean_closure_set(v___x_1321_, 2, v_a_1315_);
v___x_1322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1321_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1357_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1357_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1357_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1323_, v_e_1314_);
lean_dec(v_a_1323_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; 
lean_del_object(v___x_1325_);
v___x_1328_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1329_ = lean_box(v_usedLetOnly_1311_);
v___x_1330_ = lean_box(v_skipConstInApp_1312_);
v___x_1331_ = lean_box(v_skipInstances_1313_);
lean_inc_ref(v_e_1314_);
v___f_1332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1332_, 0, v___x_1328_);
lean_closure_set(v___f_1332_, 1, v_pre_1309_);
lean_closure_set(v___f_1332_, 2, v_e_1314_);
lean_closure_set(v___f_1332_, 3, v_post_1310_);
lean_closure_set(v___f_1332_, 4, v___x_1329_);
lean_closure_set(v___f_1332_, 5, v___x_1330_);
lean_closure_set(v___f_1332_, 6, v___x_1331_);
v___x_1333_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1332_, v_a_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc_n(v_a_1334_, 2);
lean_dec_ref_known(v___x_1333_, 1);
lean_inc(v_a_1315_);
v___f_1335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1335_, 0, v_a_1315_);
lean_closure_set(v___f_1335_, 1, v_e_1314_);
lean_closure_set(v___f_1335_, 2, v_a_1334_);
v___x_1336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1335_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1336_, 0);
lean_dec(v_unused_1344_);
v___x_1338_ = v___x_1336_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v___x_1336_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_a_1334_);
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1334_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_a_1334_);
v_a_1345_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1336_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1336_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_dec_ref(v_e_1314_);
return v___x_1333_;
}
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1355_; 
lean_dec_ref(v_e_1314_);
lean_dec_ref(v_post_1310_);
lean_dec_ref(v_pre_1309_);
v_val_1353_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1327_, 1);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_val_1353_);
v___x_1355_ = v___x_1325_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_val_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_e_1314_);
lean_dec_ref(v_post_1310_);
lean_dec_ref(v_pre_1309_);
v_a_1358_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1322_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1322_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1366_, lean_object* v_post_1367_, uint8_t v_usedLetOnly_1368_, uint8_t v_skipConstInApp_1369_, uint8_t v_skipInstances_1370_, lean_object* v_fvars_1371_, lean_object* v_e_1372_, lean_object* v_a_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
if (lean_obj_tag(v_e_1372_) == 7)
{
lean_object* v_binderName_1379_; lean_object* v_binderType_1380_; lean_object* v_body_1381_; uint8_t v_binderInfo_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_binderName_1379_ = lean_ctor_get(v_e_1372_, 0);
lean_inc(v_binderName_1379_);
v_binderType_1380_ = lean_ctor_get(v_e_1372_, 1);
lean_inc_ref(v_binderType_1380_);
v_body_1381_ = lean_ctor_get(v_e_1372_, 2);
lean_inc_ref(v_body_1381_);
v_binderInfo_1382_ = lean_ctor_get_uint8(v_e_1372_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1372_, 3);
v___x_1383_ = lean_box(v_usedLetOnly_1368_);
v___x_1384_ = lean_box(v_skipConstInApp_1369_);
v___x_1385_ = lean_box(v_skipInstances_1370_);
lean_inc_ref(v_post_1367_);
lean_inc_ref(v_pre_1366_);
lean_inc_ref(v_fvars_1371_);
v___f_1386_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1386_, 0, v_fvars_1371_);
lean_closure_set(v___f_1386_, 1, v_pre_1366_);
lean_closure_set(v___f_1386_, 2, v_post_1367_);
lean_closure_set(v___f_1386_, 3, v___x_1383_);
lean_closure_set(v___f_1386_, 4, v___x_1384_);
lean_closure_set(v___f_1386_, 5, v___x_1385_);
lean_closure_set(v___f_1386_, 6, v_body_1381_);
v___x_1387_ = lean_expr_instantiate_rev(v_binderType_1380_, v_fvars_1371_);
lean_dec_ref(v_fvars_1371_);
lean_dec_ref(v_binderType_1380_);
v___x_1388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1366_, v_post_1367_, v_usedLetOnly_1368_, v_skipConstInApp_1369_, v_skipInstances_1370_, v___x_1387_, v_a_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = 0;
v___x_1391_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1379_, v_binderInfo_1382_, v_a_1389_, v___f_1386_, v___x_1390_, v_a_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1391_;
}
else
{
lean_dec_ref(v___f_1386_);
lean_dec(v_binderName_1379_);
return v___x_1388_;
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_expr_instantiate_rev(v_e_1372_, v_fvars_1371_);
lean_dec_ref(v_e_1372_);
lean_inc_ref(v_post_1367_);
lean_inc_ref(v_pre_1366_);
v___x_1393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1366_, v_post_1367_, v_usedLetOnly_1368_, v_skipConstInApp_1369_, v_skipInstances_1370_, v___x_1392_, v_a_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; uint8_t v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = 0;
v___x_1396_ = 1;
v___x_1397_ = 1;
v___x_1398_ = l_Lean_Meta_mkForallFVars(v_fvars_1371_, v_a_1394_, v___x_1395_, v_usedLetOnly_1368_, v___x_1396_, v___x_1397_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec_ref(v_fvars_1371_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1366_, v_post_1367_, v_usedLetOnly_1368_, v_skipConstInApp_1369_, v_skipInstances_1370_, v_a_1399_, v_a_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1400_;
}
else
{
lean_dec_ref(v_post_1367_);
lean_dec_ref(v_pre_1366_);
return v___x_1398_;
}
}
else
{
lean_dec_ref(v_fvars_1371_);
lean_dec_ref(v_post_1367_);
lean_dec_ref(v_pre_1366_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1401_, lean_object* v_pre_1402_, lean_object* v_post_1403_, uint8_t v_usedLetOnly_1404_, uint8_t v_skipConstInApp_1405_, uint8_t v_skipInstances_1406_, lean_object* v_body_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_array_push(v_fvars_1401_, v_x_1408_);
v___x_1416_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v___x_1415_, v_body_1407_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1417_, lean_object* v_post_1418_, lean_object* v_usedLetOnly_1419_, lean_object* v_skipConstInApp_1420_, lean_object* v_skipInstances_1421_, lean_object* v_e_1422_, lean_object* v_a_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v_usedLetOnly_boxed_1429_; uint8_t v_skipConstInApp_boxed_1430_; uint8_t v_skipInstances_boxed_1431_; lean_object* v_res_1432_; 
v_usedLetOnly_boxed_1429_ = lean_unbox(v_usedLetOnly_1419_);
v_skipConstInApp_boxed_1430_ = lean_unbox(v_skipConstInApp_1420_);
v_skipInstances_boxed_1431_ = lean_unbox(v_skipInstances_1421_);
v_res_1432_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1417_, v_post_1418_, v_usedLetOnly_boxed_1429_, v_skipConstInApp_boxed_1430_, v_skipInstances_boxed_1431_, v_e_1422_, v_a_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v_a_1423_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1433_, lean_object* v_post_1434_, lean_object* v_usedLetOnly_1435_, lean_object* v_skipConstInApp_1436_, lean_object* v_skipInstances_1437_, lean_object* v_sz_1438_, lean_object* v_i_1439_, lean_object* v_bs_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_usedLetOnly_boxed_1447_; uint8_t v_skipConstInApp_boxed_1448_; uint8_t v_skipInstances_boxed_1449_; size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; lean_object* v_res_1452_; 
v_usedLetOnly_boxed_1447_ = lean_unbox(v_usedLetOnly_1435_);
v_skipConstInApp_boxed_1448_ = lean_unbox(v_skipConstInApp_1436_);
v_skipInstances_boxed_1449_ = lean_unbox(v_skipInstances_1437_);
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1438_);
lean_dec(v_sz_1438_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1439_);
lean_dec(v_i_1439_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1433_, v_post_1434_, v_usedLetOnly_boxed_1447_, v_skipConstInApp_boxed_1448_, v_skipInstances_boxed_1449_, v_sz_boxed_1450_, v_i_boxed_1451_, v_bs_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1453_, lean_object* v_post_1454_, lean_object* v_usedLetOnly_1455_, lean_object* v_skipConstInApp_1456_, lean_object* v_skipInstances_1457_, lean_object* v_e_1458_, lean_object* v_a_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v_usedLetOnly_boxed_1465_; uint8_t v_skipConstInApp_boxed_1466_; uint8_t v_skipInstances_boxed_1467_; lean_object* v_res_1468_; 
v_usedLetOnly_boxed_1465_ = lean_unbox(v_usedLetOnly_1455_);
v_skipConstInApp_boxed_1466_ = lean_unbox(v_skipConstInApp_1456_);
v_skipInstances_boxed_1467_ = lean_unbox(v_skipInstances_1457_);
v_res_1468_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1453_, v_post_1454_, v_usedLetOnly_boxed_1465_, v_skipConstInApp_boxed_1466_, v_skipInstances_boxed_1467_, v_e_1458_, v_a_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1459_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1469_, lean_object* v_post_1470_, lean_object* v_usedLetOnly_1471_, lean_object* v_skipConstInApp_1472_, lean_object* v_skipInstances_1473_, lean_object* v_fvars_1474_, lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_usedLetOnly_boxed_1482_; uint8_t v_skipConstInApp_boxed_1483_; uint8_t v_skipInstances_boxed_1484_; lean_object* v_res_1485_; 
v_usedLetOnly_boxed_1482_ = lean_unbox(v_usedLetOnly_1471_);
v_skipConstInApp_boxed_1483_ = lean_unbox(v_skipConstInApp_1472_);
v_skipInstances_boxed_1484_ = lean_unbox(v_skipInstances_1473_);
v_res_1485_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1469_, v_post_1470_, v_usedLetOnly_boxed_1482_, v_skipConstInApp_boxed_1483_, v_skipInstances_boxed_1484_, v_fvars_1474_, v_e_1475_, v_a_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_a_1476_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1486_, lean_object* v_post_1487_, lean_object* v_usedLetOnly_1488_, lean_object* v_skipConstInApp_1489_, lean_object* v_skipInstances_1490_, lean_object* v_fvars_1491_, lean_object* v_e_1492_, lean_object* v_a_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_usedLetOnly_boxed_1499_; uint8_t v_skipConstInApp_boxed_1500_; uint8_t v_skipInstances_boxed_1501_; lean_object* v_res_1502_; 
v_usedLetOnly_boxed_1499_ = lean_unbox(v_usedLetOnly_1488_);
v_skipConstInApp_boxed_1500_ = lean_unbox(v_skipConstInApp_1489_);
v_skipInstances_boxed_1501_ = lean_unbox(v_skipInstances_1490_);
v_res_1502_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1486_, v_post_1487_, v_usedLetOnly_boxed_1499_, v_skipConstInApp_boxed_1500_, v_skipInstances_boxed_1501_, v_fvars_1491_, v_e_1492_, v_a_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v_a_1493_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1503_, lean_object* v_post_1504_, lean_object* v_usedLetOnly_1505_, lean_object* v_skipConstInApp_1506_, lean_object* v_skipInstances_1507_, lean_object* v_fvars_1508_, lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v_usedLetOnly_boxed_1516_; uint8_t v_skipConstInApp_boxed_1517_; uint8_t v_skipInstances_boxed_1518_; lean_object* v_res_1519_; 
v_usedLetOnly_boxed_1516_ = lean_unbox(v_usedLetOnly_1505_);
v_skipConstInApp_boxed_1517_ = lean_unbox(v_skipConstInApp_1506_);
v_skipInstances_boxed_1518_ = lean_unbox(v_skipInstances_1507_);
v_res_1519_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1503_, v_post_1504_, v_usedLetOnly_boxed_1516_, v_skipConstInApp_boxed_1517_, v_skipInstances_boxed_1518_, v_fvars_1508_, v_e_1509_, v_a_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_a_1510_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1520_, lean_object* v___x_1521_, lean_object* v_pre_1522_, lean_object* v_post_1523_, lean_object* v_usedLetOnly_1524_, lean_object* v_skipConstInApp_1525_, lean_object* v_skipInstances_1526_, lean_object* v_a_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_usedLetOnly_boxed_1535_; uint8_t v_skipConstInApp_boxed_1536_; uint8_t v_skipInstances_boxed_1537_; lean_object* v_res_1538_; 
v_usedLetOnly_boxed_1535_ = lean_unbox(v_usedLetOnly_1524_);
v_skipConstInApp_boxed_1536_ = lean_unbox(v_skipConstInApp_1525_);
v_skipInstances_boxed_1537_ = lean_unbox(v_skipInstances_1526_);
v_res_1538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1520_, v___x_1521_, v_pre_1522_, v_post_1523_, v_usedLetOnly_boxed_1535_, v_skipConstInApp_boxed_1536_, v_skipInstances_boxed_1537_, v_a_1527_, v_b_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___x_1521_);
lean_dec(v_upperBound_1520_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1539_, lean_object* v_pre_1540_, lean_object* v_post_1541_, lean_object* v_usedLetOnly_1542_, lean_object* v_skipConstInApp_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_skipInstances_boxed_1553_; uint8_t v_usedLetOnly_boxed_1554_; uint8_t v_skipConstInApp_boxed_1555_; lean_object* v_res_1556_; 
v_skipInstances_boxed_1553_ = lean_unbox(v_skipInstances_1539_);
v_usedLetOnly_boxed_1554_ = lean_unbox(v_usedLetOnly_1542_);
v_skipConstInApp_boxed_1555_ = lean_unbox(v_skipConstInApp_1543_);
v_res_1556_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1553_, v_pre_1540_, v_post_1541_, v_usedLetOnly_boxed_1554_, v_skipConstInApp_boxed_1555_, v_x_1544_, v_x_1545_, v_x_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
return v_res_1556_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_unsigned_to_nat(16u);
v___x_1559_ = lean_mk_array(v___x_1558_, v___x_1557_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1560_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1564_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1564_, 0, lean_box(0));
lean_closure_set(v___x_1564_, 1, lean_box(0));
lean_closure_set(v___x_1564_, 2, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1565_, lean_object* v_pre_1566_, lean_object* v_post_1567_, uint8_t v_usedLetOnly_1568_, uint8_t v_skipConstInApp_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1579_; 
v___x_1575_ = 0;
v___x_1576_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1577_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1576_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1566_, v_post_1567_, v_usedLetOnly_1568_, v_skipConstInApp_1569_, v___x_1575_, v_input_1565_, v_a_1578_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1581_, 0, lean_box(0));
lean_closure_set(v___x_1581_, 1, lean_box(0));
lean_closure_set(v___x_1581_, 2, v_a_1578_);
v___x_1582_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1581_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v___x_1582_, 0);
lean_dec(v_unused_1590_);
v___x_1584_ = v___x_1582_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v___x_1582_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v_a_1580_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1580_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
else
{
lean_dec(v_a_1578_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1591_, lean_object* v_pre_1592_, lean_object* v_post_1593_, lean_object* v_usedLetOnly_1594_, lean_object* v_skipConstInApp_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_usedLetOnly_boxed_1601_; uint8_t v_skipConstInApp_boxed_1602_; lean_object* v_res_1603_; 
v_usedLetOnly_boxed_1601_ = lean_unbox(v_usedLetOnly_1594_);
v_skipConstInApp_boxed_1602_ = lean_unbox(v_skipConstInApp_1595_);
v_res_1603_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1591_, v_pre_1592_, v_post_1593_, v_usedLetOnly_boxed_1601_, v_skipConstInApp_boxed_1602_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1625_; 
v___f_1612_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1613_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1606_, v_a_1610_);
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_unbox(v_a_1614_);
lean_dec(v_a_1614_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1620_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v_e_1606_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_e_1606_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1616_);
v___x_1622_ = 0;
v___x_1623_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1624_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1606_, v___x_1623_, v___f_1612_, v___x_1622_, v___x_1622_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
return v___x_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1633_, lean_object* v___x_1634_, lean_object* v_pre_1635_, lean_object* v_post_1636_, uint8_t v_usedLetOnly_1637_, uint8_t v_skipConstInApp_1638_, uint8_t v_skipInstances_1639_, lean_object* v___x_1640_, lean_object* v_inst_1641_, lean_object* v_R_1642_, lean_object* v_a_1643_, lean_object* v_b_1644_, lean_object* v_c_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1633_, v___x_1634_, v_pre_1635_, v_post_1636_, v_usedLetOnly_1637_, v_skipConstInApp_1638_, v_skipInstances_1639_, v_a_1643_, v_b_1644_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1653_ = _args[0];
lean_object* v___x_1654_ = _args[1];
lean_object* v_pre_1655_ = _args[2];
lean_object* v_post_1656_ = _args[3];
lean_object* v_usedLetOnly_1657_ = _args[4];
lean_object* v_skipConstInApp_1658_ = _args[5];
lean_object* v_skipInstances_1659_ = _args[6];
lean_object* v___x_1660_ = _args[7];
lean_object* v_inst_1661_ = _args[8];
lean_object* v_R_1662_ = _args[9];
lean_object* v_a_1663_ = _args[10];
lean_object* v_b_1664_ = _args[11];
lean_object* v_c_1665_ = _args[12];
lean_object* v___y_1666_ = _args[13];
lean_object* v___y_1667_ = _args[14];
lean_object* v___y_1668_ = _args[15];
lean_object* v___y_1669_ = _args[16];
lean_object* v___y_1670_ = _args[17];
lean_object* v___y_1671_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1672_; uint8_t v_skipConstInApp_boxed_1673_; uint8_t v_skipInstances_boxed_1674_; lean_object* v_res_1675_; 
v_usedLetOnly_boxed_1672_ = lean_unbox(v_usedLetOnly_1657_);
v_skipConstInApp_boxed_1673_ = lean_unbox(v_skipConstInApp_1658_);
v_skipInstances_boxed_1674_ = lean_unbox(v_skipInstances_1659_);
v_res_1675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1653_, v___x_1654_, v_pre_1655_, v_post_1656_, v_usedLetOnly_boxed_1672_, v_skipConstInApp_boxed_1673_, v_skipInstances_boxed_1674_, v___x_1660_, v_inst_1661_, v_R_1662_, v_a_1663_, v_b_1664_, v_c_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec(v___x_1660_);
lean_dec_ref(v___x_1654_);
lean_dec(v_upperBound_1653_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1676_, lean_object* v_m_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1677_, v_a_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1680_, lean_object* v_m_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1680_, v_m_1681_, v_a_1682_);
lean_dec_ref(v_a_1682_);
lean_dec_ref(v_m_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1684_, lean_object* v_name_1685_, uint8_t v_bi_1686_, lean_object* v_type_1687_, lean_object* v_k_1688_, uint8_t v_kind_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1685_, v_bi_1686_, v_type_1687_, v_k_1688_, v_kind_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_name_1698_, lean_object* v_bi_1699_, lean_object* v_type_1700_, lean_object* v_k_1701_, lean_object* v_kind_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v_bi_boxed_1709_; uint8_t v_kind_boxed_1710_; lean_object* v_res_1711_; 
v_bi_boxed_1709_ = lean_unbox(v_bi_1699_);
v_kind_boxed_1710_ = lean_unbox(v_kind_1702_);
v_res_1711_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1697_, v_name_1698_, v_bi_boxed_1709_, v_type_1700_, v_k_1701_, v_kind_boxed_1710_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1712_, lean_object* v_name_1713_, lean_object* v_type_1714_, lean_object* v_val_1715_, lean_object* v_k_1716_, uint8_t v_nondep_1717_, uint8_t v_kind_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1713_, v_type_1714_, v_val_1715_, v_k_1716_, v_nondep_1717_, v_kind_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1726_, lean_object* v_name_1727_, lean_object* v_type_1728_, lean_object* v_val_1729_, lean_object* v_k_1730_, lean_object* v_nondep_1731_, lean_object* v_kind_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v_nondep_boxed_1739_; uint8_t v_kind_boxed_1740_; lean_object* v_res_1741_; 
v_nondep_boxed_1739_ = lean_unbox(v_nondep_1731_);
v_kind_boxed_1740_ = lean_unbox(v_kind_1732_);
v_res_1741_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1726_, v_name_1727_, v_type_1728_, v_val_1729_, v_k_1730_, v_nondep_boxed_1739_, v_kind_boxed_1740_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1742_, lean_object* v_ref_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1743_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_ref_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1750_, v_ref_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_x_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1767_, v_x_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1776_, lean_object* v_m_1777_, lean_object* v_a_1778_, lean_object* v_b_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1777_, v_a_1778_, v_b_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1781_, lean_object* v_a_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1782_, v_x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1785_, lean_object* v_a_1786_, lean_object* v_x_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1785_, v_a_1786_, v_x_1787_);
lean_dec(v_x_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1789_, lean_object* v_a_1790_, lean_object* v_x_1791_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1790_, v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1793_, lean_object* v_a_1794_, lean_object* v_x_1795_){
_start:
{
uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_res_1796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1793_, v_a_1794_, v_x_1795_);
lean_dec(v_x_1795_);
lean_dec_ref(v_a_1794_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1798_, lean_object* v_data_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1801_, lean_object* v_a_1802_, lean_object* v_b_1803_, lean_object* v_x_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1802_, v_b_1803_, v_x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1806_, lean_object* v_i_1807_, lean_object* v_source_1808_, lean_object* v_target_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1807_, v_source_1808_, v_target_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1812_, v_x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v_x_1823_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v_env_1837_; uint8_t v___x_1838_; lean_object* v_env_1839_; lean_object* v___x_1840_; lean_object* v_toCold_1841_; lean_object* v_mctx_1842_; lean_object* v_lctx_1843_; lean_object* v_options_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1836_ = lean_st_ref_get(v___y_1834_);
v_env_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc_ref(v_env_1837_);
lean_dec(v___x_1836_);
v___x_1838_ = 0;
v_env_1839_ = l_Lean_Environment_setRecordingDeps(v_env_1837_, v___x_1838_);
v___x_1840_ = lean_st_ref_get(v___y_1832_);
v_toCold_1841_ = lean_ctor_get(v___y_1833_, 0);
v_mctx_1842_ = lean_ctor_get(v___x_1840_, 0);
lean_inc_ref(v_mctx_1842_);
lean_dec(v___x_1840_);
v_lctx_1843_ = lean_ctor_get(v___y_1831_, 2);
v_options_1844_ = lean_ctor_get(v_toCold_1841_, 2);
lean_inc_ref(v_options_1844_);
lean_inc_ref(v_lctx_1843_);
v___x_1845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1845_, 0, v_env_1839_);
lean_ctor_set(v___x_1845_, 1, v_mctx_1842_);
lean_ctor_set(v___x_1845_, 2, v_lctx_1843_);
lean_ctor_set(v___x_1845_, 3, v_options_1844_);
v___x_1846_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_msgData_1830_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1855_; double v___x_1856_; 
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_float_of_nat(v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1860_, lean_object* v_msg_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_ref_1867_; lean_object* v___x_1868_; lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1914_; 
v_ref_1867_ = lean_ctor_get(v___y_1864_, 2);
v___x_1868_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1914_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1914_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v_traceState_1874_; lean_object* v_env_1875_; lean_object* v_nextMacroScope_1876_; lean_object* v_ngen_1877_; lean_object* v_auxDeclNGen_1878_; lean_object* v_cache_1879_; lean_object* v_recordedDeps_1880_; lean_object* v_messages_1881_; lean_object* v_infoState_1882_; lean_object* v_snapshotTasks_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1913_; 
v___x_1873_ = lean_st_ref_take(v___y_1865_);
v_traceState_1874_ = lean_ctor_get(v___x_1873_, 4);
v_env_1875_ = lean_ctor_get(v___x_1873_, 0);
v_nextMacroScope_1876_ = lean_ctor_get(v___x_1873_, 1);
v_ngen_1877_ = lean_ctor_get(v___x_1873_, 2);
v_auxDeclNGen_1878_ = lean_ctor_get(v___x_1873_, 3);
v_cache_1879_ = lean_ctor_get(v___x_1873_, 5);
v_recordedDeps_1880_ = lean_ctor_get(v___x_1873_, 6);
v_messages_1881_ = lean_ctor_get(v___x_1873_, 7);
v_infoState_1882_ = lean_ctor_get(v___x_1873_, 8);
v_snapshotTasks_1883_ = lean_ctor_get(v___x_1873_, 9);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1885_ = v___x_1873_;
v_isShared_1886_ = v_isSharedCheck_1913_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snapshotTasks_1883_);
lean_inc(v_infoState_1882_);
lean_inc(v_messages_1881_);
lean_inc(v_recordedDeps_1880_);
lean_inc(v_cache_1879_);
lean_inc(v_traceState_1874_);
lean_inc(v_auxDeclNGen_1878_);
lean_inc(v_ngen_1877_);
lean_inc(v_nextMacroScope_1876_);
lean_inc(v_env_1875_);
lean_dec(v___x_1873_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1913_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
uint64_t v_tid_1887_; lean_object* v_traces_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1912_; 
v_tid_1887_ = lean_ctor_get_uint64(v_traceState_1874_, sizeof(void*)*1);
v_traces_1888_ = lean_ctor_get(v_traceState_1874_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_traceState_1874_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1890_ = v_traceState_1874_;
v_isShared_1891_ = v_isSharedCheck_1912_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_traces_1888_);
lean_dec(v_traceState_1874_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1912_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; double v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1895_ = 0;
v___x_1896_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1897_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1897_, 0, v_cls_1860_);
lean_ctor_set(v___x_1897_, 1, v___x_1893_);
lean_ctor_set(v___x_1897_, 2, v___x_1896_);
lean_ctor_set_float(v___x_1897_, sizeof(void*)*3, v___x_1894_);
lean_ctor_set_float(v___x_1897_, sizeof(void*)*3 + 8, v___x_1894_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*3 + 16, v___x_1895_);
v___x_1898_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1899_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v_a_1869_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
lean_inc(v_ref_1867_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_ref_1867_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_PersistentArray_push___redArg(v_traces_1888_, v___x_1900_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1901_);
v___x_1903_ = v___x_1890_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1901_);
lean_ctor_set_uint64(v_reuseFailAlloc_1911_, sizeof(void*)*1, v_tid_1887_);
v___x_1903_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 4, v___x_1903_);
v___x_1905_ = v___x_1885_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_env_1875_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_nextMacroScope_1876_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_ngen_1877_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_auxDeclNGen_1878_);
lean_ctor_set(v_reuseFailAlloc_1910_, 4, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1910_, 5, v_cache_1879_);
lean_ctor_set(v_reuseFailAlloc_1910_, 6, v_recordedDeps_1880_);
lean_ctor_set(v_reuseFailAlloc_1910_, 7, v_messages_1881_);
lean_ctor_set(v_reuseFailAlloc_1910_, 8, v_infoState_1882_);
lean_ctor_set(v_reuseFailAlloc_1910_, 9, v_snapshotTasks_1883_);
v___x_1905_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_st_ref_put(v___y_1865_, v___x_1905_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1892_);
v___x_1908_ = v___x_1871_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1892_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1915_, lean_object* v_msg_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1915_, v_msg_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__1));
v___x_1928_ = l_Lean_Name_append(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__3));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__5));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__7));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__9));
v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_e_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___y_1948_; 
if (lean_obj_tag(v_e_1941_) == 11)
{
lean_object* v_typeName_1972_; lean_object* v_idx_1973_; lean_object* v_struct_1974_; lean_object* v___x_1975_; lean_object* v_env_1976_; lean_object* v___x_1977_; 
v_typeName_1972_ = lean_ctor_get(v_e_1941_, 0);
v_idx_1973_ = lean_ctor_get(v_e_1941_, 1);
v_struct_1974_ = lean_ctor_get(v_e_1941_, 2);
v___x_1975_ = lean_st_ref_get(v___y_1945_);
v_env_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref(v_env_1976_);
lean_dec(v___x_1975_);
lean_inc(v_typeName_1972_);
v___x_1977_ = l_Lean_getStructureInfo_x3f(v_env_1976_, v_typeName_1972_);
if (lean_obj_tag(v___x_1977_) == 1)
{
lean_object* v_val_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2032_; 
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2032_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_val_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2032_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_fieldNames_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_fieldNames_1982_ = lean_ctor_get(v_val_1978_, 1);
lean_inc_ref(v_fieldNames_1982_);
lean_dec(v_val_1978_);
v___x_1983_ = lean_array_get_size(v_fieldNames_1982_);
v___x_1984_ = lean_nat_dec_lt(v_idx_1973_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v_toCold_1985_; lean_object* v_options_1986_; uint8_t v_hasTrace_1987_; 
lean_dec_ref(v_fieldNames_1982_);
v_toCold_1985_ = lean_ctor_get(v___y_1944_, 0);
v_options_1986_ = lean_ctor_get(v_toCold_1985_, 2);
v_hasTrace_1987_ = lean_ctor_get_uint8(v_options_1986_, sizeof(void*)*1);
if (v_hasTrace_1987_ == 0)
{
lean_del_object(v___x_1980_);
goto v___jp_1969_;
}
else
{
lean_object* v_inheritedTraceOptions_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_inheritedTraceOptions_1988_ = lean_ctor_get(v_toCold_1985_, 11);
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1990_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_1991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1988_, v_options_1986_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_del_object(v___x_1980_);
goto v___jp_1969_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4);
lean_inc(v_idx_1973_);
v___x_1993_ = l_Nat_reprFast(v_idx_1973_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 3);
lean_ctor_set(v___x_1980_, 0, v___x_1993_);
v___x_1995_ = v___x_1980_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2011_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1996_ = l_Lean_MessageData_ofFormat(v___x_1995_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1992_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
lean_inc_ref(v_e_1941_);
v___x_2000_ = l_Lean_indentExpr(v_e_1941_);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1989_, v___x_2001_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_dec_ref_known(v___x_2002_, 1);
goto v___jp_1969_;
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref_known(v_e_1941_, 3);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2012_; uint8_t v_transparency_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; uint8_t v___x_2016_; 
lean_inc_ref(v_struct_1974_);
lean_inc(v_idx_1973_);
lean_del_object(v___x_1980_);
lean_dec_ref_known(v_e_1941_, 3);
v___x_2012_ = l_Lean_Meta_Context_config(v___y_1942_);
v_transparency_2013_ = lean_ctor_get_uint8(v___x_2012_, 9);
lean_dec_ref(v___x_2012_);
v___x_2014_ = lean_array_fget(v_fieldNames_1982_, v_idx_1973_);
lean_dec(v_idx_1973_);
lean_dec_ref(v_fieldNames_1982_);
v___x_2015_ = 1;
v___x_2016_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2013_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v_keyedConfig_2017_; uint8_t v_trackZetaDelta_2018_; lean_object* v_zetaDeltaSet_2019_; lean_object* v_lctx_2020_; lean_object* v_localInstances_2021_; lean_object* v_defEqCtx_x3f_2022_; lean_object* v_synthPendingDepth_2023_; lean_object* v_customCanUnfoldPredicate_x3f_2024_; uint8_t v_univApprox_2025_; uint8_t v_inTypeClassResolution_2026_; uint8_t v_cacheInferType_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_keyedConfig_2017_ = lean_ctor_get(v___y_1942_, 0);
v_trackZetaDelta_2018_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*7);
v_zetaDeltaSet_2019_ = lean_ctor_get(v___y_1942_, 1);
v_lctx_2020_ = lean_ctor_get(v___y_1942_, 2);
v_localInstances_2021_ = lean_ctor_get(v___y_1942_, 3);
v_defEqCtx_x3f_2022_ = lean_ctor_get(v___y_1942_, 4);
v_synthPendingDepth_2023_ = lean_ctor_get(v___y_1942_, 5);
v_customCanUnfoldPredicate_x3f_2024_ = lean_ctor_get(v___y_1942_, 6);
v_univApprox_2025_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2026_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*7 + 2);
v_cacheInferType_2027_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2017_);
v___x_2028_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2015_, v_keyedConfig_2017_);
lean_inc(v_customCanUnfoldPredicate_x3f_2024_);
lean_inc(v_synthPendingDepth_2023_);
lean_inc(v_defEqCtx_x3f_2022_);
lean_inc_ref(v_localInstances_2021_);
lean_inc_ref(v_lctx_2020_);
lean_inc(v_zetaDeltaSet_2019_);
v___x_2029_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v_zetaDeltaSet_2019_);
lean_ctor_set(v___x_2029_, 2, v_lctx_2020_);
lean_ctor_set(v___x_2029_, 3, v_localInstances_2021_);
lean_ctor_set(v___x_2029_, 4, v_defEqCtx_x3f_2022_);
lean_ctor_set(v___x_2029_, 5, v_synthPendingDepth_2023_);
lean_ctor_set(v___x_2029_, 6, v_customCanUnfoldPredicate_x3f_2024_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*7, v_trackZetaDelta_2018_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*7 + 1, v_univApprox_2025_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2026_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*7 + 3, v_cacheInferType_2027_);
v___x_2030_ = l_Lean_Meta_mkProjection(v_struct_1974_, v___x_2014_, v___x_2029_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec_ref_known(v___x_2029_, 7);
v___y_1948_ = v___x_2030_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Meta_mkProjection(v_struct_1974_, v___x_2014_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
v___y_1948_ = v___x_2031_;
goto v___jp_1947_;
}
}
}
}
else
{
lean_object* v_toCold_2033_; lean_object* v_options_2034_; uint8_t v_hasTrace_2035_; 
lean_dec(v___x_1977_);
v_toCold_2033_ = lean_ctor_get(v___y_1944_, 0);
v_options_2034_ = lean_ctor_get(v_toCold_2033_, 2);
v_hasTrace_2035_ = lean_ctor_get_uint8(v_options_2034_, sizeof(void*)*1);
if (v_hasTrace_2035_ == 0)
{
goto v___jp_1966_;
}
else
{
lean_object* v_inheritedTraceOptions_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_inheritedTraceOptions_2036_ = lean_ctor_get(v_toCold_2033_, 11);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2038_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2036_, v_options_2034_, v___x_2038_);
if (v___x_2039_ == 0)
{
goto v___jp_1966_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2040_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8);
lean_inc(v_typeName_1972_);
v___x_2041_ = l_Lean_MessageData_ofName(v_typeName_1972_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_inc_ref(v_e_1941_);
v___x_2045_ = l_Lean_indentExpr(v_e_1941_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2037_, v___x_2046_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_dec_ref_known(v___x_2047_, 1);
goto v___jp_1966_;
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref_known(v_e_1941_, 3);
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_e_1941_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
v___jp_1947_:
{
if (lean_obj_tag(v___y_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_a_1949_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v___y_1948_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___y_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_a_1958_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___y_1948_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___y_1948_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
v___jp_1966_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_e_1941_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
v___jp_1969_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_e_1941_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_e_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___f_2074_; lean_object* v___x_2075_; 
v___f_2074_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2075_ = lean_find_expr(v___f_2074_, v_e_2068_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_e_2068_);
return v___x_2076_;
}
else
{
lean_object* v___f_2077_; lean_object* v_post_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref_known(v___x_2075_, 1);
v___f_2077_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v_post_2078_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2079_ = 0;
v___x_2080_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2068_, v___f_2077_, v_post_2078_, v___x_2079_, v___x_2079_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Meta_Sym_foldProjs(v_e_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2093_ = l_Lean_mkConst(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_box(0);
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2099_ = l_Lean_mkConst(v___x_2098_, v___x_2097_);
return v___x_2099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2107_ = l_Lean_mkConst(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_box(0);
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2114_ = l_Lean_mkConst(v___x_2113_, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = l_Lean_mkNatLit(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2124_ = l_Lean_mkConst(v___x_2123_, v___x_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2128_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2127_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
v_a_2130_ = lean_ctor_get(v___x_2128_, 1);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2128_, 2);
v___x_2131_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2132_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2131_, v_a_2125_, v_a_2130_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
v_a_2134_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2132_, 2);
v___x_2135_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2136_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2135_, v_a_2125_, v_a_2134_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
v_a_2138_ = lean_ctor_get(v___x_2136_, 1);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2136_, 2);
v___x_2139_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2140_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2139_, v_a_2125_, v_a_2138_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
v_a_2142_ = lean_ctor_get(v___x_2140_, 1);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2140_, 2);
v___x_2143_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2144_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2143_, v_a_2125_, v_a_2142_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
v_a_2146_ = lean_ctor_get(v___x_2144_, 1);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2144_, 2);
v___x_2147_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2148_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2147_, v_a_2125_, v_a_2146_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
v_a_2150_ = lean_ctor_get(v___x_2148_, 1);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2148_, 2);
v___x_2151_ = l_Lean_Int_mkType;
v___x_2152_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2151_, v_a_2125_, v_a_2150_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2162_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_a_2154_ = lean_ctor_get(v___x_2152_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2156_ = v___x_2152_;
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2158_, 0, v_a_2133_);
lean_ctor_set(v___x_2158_, 1, v_a_2129_);
lean_ctor_set(v___x_2158_, 2, v_a_2145_);
lean_ctor_set(v___x_2158_, 3, v_a_2141_);
lean_ctor_set(v___x_2158_, 4, v_a_2137_);
lean_ctor_set(v___x_2158_, 5, v_a_2149_);
lean_ctor_set(v___x_2158_, 6, v_a_2153_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2158_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2154_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_a_2149_);
lean_dec(v_a_2145_);
lean_dec(v_a_2141_);
lean_dec(v_a_2137_);
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
v_a_2163_ = lean_ctor_get(v___x_2152_, 0);
v_a_2164_ = lean_ctor_get(v___x_2152_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2152_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_inc(v_a_2163_);
lean_dec(v___x_2152_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2145_);
lean_dec(v_a_2141_);
lean_dec(v_a_2137_);
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
v_a_2172_ = lean_ctor_get(v___x_2148_, 0);
v_a_2173_ = lean_ctor_get(v___x_2148_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2148_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_inc(v_a_2172_);
lean_dec(v___x_2148_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2172_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2141_);
lean_dec(v_a_2137_);
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
v_a_2181_ = lean_ctor_get(v___x_2144_, 0);
v_a_2182_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2144_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_inc(v_a_2181_);
lean_dec(v___x_2144_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2181_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_a_2137_);
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
v_a_2190_ = lean_ctor_get(v___x_2140_, 0);
v_a_2191_ = lean_ctor_get(v___x_2140_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2140_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_inc(v_a_2190_);
lean_dec(v___x_2140_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2190_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2133_);
lean_dec(v_a_2129_);
v_a_2199_ = lean_ctor_get(v___x_2136_, 0);
v_a_2200_ = lean_ctor_get(v___x_2136_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2136_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_inc(v_a_2199_);
lean_dec(v___x_2136_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2129_);
v_a_2208_ = lean_ctor_get(v___x_2132_, 0);
v_a_2209_ = lean_ctor_get(v___x_2132_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2132_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_inc(v_a_2208_);
lean_dec(v___x_2132_);
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
v_a_2217_ = lean_ctor_get(v___x_2128_, 0);
v_a_2218_ = lean_ctor_get(v___x_2128_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2128_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_inc(v_a_2217_);
lean_dec(v___x_2128_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2226_, v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2229_, lean_object* v_opt_2230_){
_start:
{
lean_object* v_name_2231_; lean_object* v_defValue_2232_; lean_object* v_map_2233_; lean_object* v___x_2234_; 
v_name_2231_ = lean_ctor_get(v_opt_2230_, 0);
v_defValue_2232_ = lean_ctor_get(v_opt_2230_, 1);
v_map_2233_ = lean_ctor_get(v_opts_2229_, 0);
v___x_2234_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2233_, v_name_2231_);
if (lean_obj_tag(v___x_2234_) == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_unbox(v_defValue_2232_);
return v___x_2235_;
}
else
{
lean_object* v_val_2236_; 
v_val_2236_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v___x_2234_, 1);
if (lean_obj_tag(v_val_2236_) == 1)
{
uint8_t v_v_2237_; 
v_v_2237_ = lean_ctor_get_uint8(v_val_2236_, 0);
lean_dec_ref_known(v_val_2236_, 0);
return v_v_2237_;
}
else
{
uint8_t v___x_2238_; 
lean_dec(v_val_2236_);
v___x_2238_ = lean_unbox(v_defValue_2232_);
return v___x_2238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2239_, lean_object* v_opt_2240_){
_start:
{
uint8_t v_res_2241_; lean_object* v_r_2242_; 
v_res_2241_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2239_, v_opt_2240_);
lean_dec_ref(v_opt_2240_);
lean_dec_ref(v_opts_2239_);
v_r_2242_ = lean_box(v_res_2241_);
return v_r_2242_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg(){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object* v___dummy_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v_res_2249_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___f_2260_; lean_object* v___x_2211__overap_2261_; lean_object* v___x_2262_; 
v___f_2260_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2211__overap_2261_ = lean_panic_fn_borrowed(v___f_2260_, v_msg_2254_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
v___x_2262_ = lean_apply_5(v___x_2211__overap_2261_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, lean_box(0));
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
return v_res_2269_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2277_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2278_ = lean_unsigned_to_nat(19u);
v___x_2279_ = lean_unsigned_to_nat(309u);
v___x_2280_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__3));
v___x_2281_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_2282_ = l_mkPanicMessageWithDecl(v___x_2281_, v___x_2280_, v___x_2279_, v___x_2278_, v___x_2277_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_fst_2290_; lean_object* v_snd_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___x_2331_; lean_object* v_env_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2331_ = lean_st_ref_get(v_a_2287_);
v_env_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc_ref(v_env_2332_);
lean_dec(v___x_2331_);
v___x_2333_ = 0;
v___x_2334_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2334_, 0, v_env_2332_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*1, v___x_2333_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*1 + 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2336_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2334_, v___x_2335_);
lean_dec_ref_known(v___x_2334_, 1);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v_a_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
v_a_2338_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2336_, 2);
v_fst_2290_ = v_a_2337_;
v_snd_2291_ = v_a_2338_;
v___y_2292_ = v_a_2284_;
v___y_2293_ = v_a_2285_;
v___y_2294_ = v_a_2286_;
v___y_2295_ = v_a_2287_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec_ref_known(v___x_2336_, 2);
v___x_2339_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__5, &l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5);
v___x_2340_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2339_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_fst_2342_; lean_object* v_snd_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v_fst_2342_ = lean_ctor_get(v_a_2341_, 0);
lean_inc(v_fst_2342_);
v_snd_2343_ = lean_ctor_get(v_a_2341_, 1);
lean_inc(v_snd_2343_);
lean_dec(v_a_2341_);
v_fst_2290_ = v_fst_2342_;
v_snd_2291_ = v_snd_2343_;
v___y_2292_ = v_a_2284_;
v___y_2293_ = v_a_2285_;
v___y_2294_ = v_a_2286_;
v___y_2295_ = v_a_2287_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v_x_2283_);
v_a_2344_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2340_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2340_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
v___jp_2289_:
{
lean_object* v_ref_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; 
v_ref_2296_ = lean_ctor_get(v___y_2294_, 2);
v___x_2297_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2294_);
v___x_2298_ = l_Lean_Meta_Sym_sym_debug;
v___x_2299_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v___x_2297_, v___x_2298_);
lean_dec_ref(v___x_2297_);
v___x_2300_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v_fst_2290_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2307_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v___x_2307_, 0, v_snd_2291_);
lean_ctor_set(v___x_2307_, 1, v___x_2304_);
lean_ctor_set(v___x_2307_, 2, v___x_2304_);
lean_ctor_set(v___x_2307_, 3, v___x_2304_);
lean_ctor_set(v___x_2307_, 4, v___x_2304_);
lean_ctor_set(v___x_2307_, 5, v___x_2304_);
lean_ctor_set(v___x_2307_, 6, v___x_2304_);
lean_ctor_set(v___x_2307_, 7, v___x_2304_);
lean_ctor_set(v___x_2307_, 8, v___x_2304_);
lean_ctor_set(v___x_2307_, 9, v_a_2301_);
lean_ctor_set(v___x_2307_, 10, v___x_2305_);
lean_ctor_set(v___x_2307_, 11, v___x_2306_);
lean_ctor_set(v___x_2307_, 12, v___x_2304_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*13, v___x_2299_);
v___x_2308_ = lean_st_mk_ref(v___x_2307_);
lean_inc(v___y_2295_);
lean_inc_ref(v___y_2294_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2292_);
lean_inc(v___x_2308_);
v___x_2309_ = lean_apply_7(v_x_2283_, v___x_2303_, v___x_2308_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, lean_box(0));
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2318_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_st_ref_get(v___x_2308_);
lean_dec(v___x_2308_);
lean_dec(v___x_2314_);
if (v_isShared_2313_ == 0)
{
v___x_2316_ = v___x_2312_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2310_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
else
{
lean_dec(v___x_2308_);
return v___x_2309_;
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_snd_2291_);
lean_dec_ref(v_fst_2290_);
lean_dec_ref(v_x_2283_);
v_a_2319_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2321_ = v___x_2300_;
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2300_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2323_ = lean_io_error_to_string(v_a_2319_);
v___x_2324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
v___x_2325_ = l_Lean_MessageData_ofFormat(v___x_2324_);
lean_inc(v_ref_2296_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_ref_2296_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2326_);
v___x_2328_ = v___x_2321_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2359_, lean_object* v_x_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_x_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2367_, v_x_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2375_){
_start:
{
lean_object* v_sharedExprs_2377_; lean_object* v___x_2378_; 
v_sharedExprs_2377_ = lean_ctor_get(v_a_2375_, 0);
lean_inc_ref(v_sharedExprs_2377_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_sharedExprs_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2379_);
lean_dec_ref(v_a_2379_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2382_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2409_; 
v___x_2400_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2398_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_trueExpr_2405_; lean_object* v___x_2407_; 
v_trueExpr_2405_ = lean_ctor_get(v_a_2401_, 0);
lean_inc_ref(v_trueExpr_2405_);
lean_dec(v_a_2401_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v_trueExpr_2405_);
v___x_2407_ = v___x_2403_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_trueExpr_2405_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2410_);
lean_dec_ref(v_a_2410_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2413_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2430_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2444_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2444_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2444_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
size_t v___x_2437_; size_t v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2437_ = lean_ptr_addr(v_e_2429_);
v___x_2438_ = lean_ptr_addr(v_a_2433_);
lean_dec(v_a_2433_);
v___x_2439_ = lean_usize_dec_eq(v___x_2437_, v___x_2438_);
v___x_2440_ = lean_box(v___x_2439_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2440_);
v___x_2442_ = v___x_2435_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
v_a_2445_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2432_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2432_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2453_, v_a_2454_);
lean_dec_ref(v_a_2454_);
lean_dec_ref(v_e_2453_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2457_, v_a_2458_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec_ref(v_e_2466_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2486_; 
v___x_2477_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2475_);
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_falseExpr_2482_; lean_object* v___x_2484_; 
v_falseExpr_2482_ = lean_ctor_get(v_a_2478_, 1);
lean_inc_ref(v_falseExpr_2482_);
lean_dec(v_a_2478_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_falseExpr_2482_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_falseExpr_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2487_);
lean_dec_ref(v_a_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2490_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2507_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2521_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
size_t v___x_2514_; size_t v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2514_ = lean_ptr_addr(v_e_2506_);
v___x_2515_ = lean_ptr_addr(v_a_2510_);
lean_dec(v_a_2510_);
v___x_2516_ = lean_usize_dec_eq(v___x_2514_, v___x_2515_);
v___x_2517_ = lean_box(v___x_2516_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2517_);
v___x_2519_ = v___x_2512_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
v_a_2522_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2509_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2509_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2530_, v_a_2531_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_e_2530_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2534_, v_a_2535_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_e_2543_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
v___x_2554_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2552_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_btrueExpr_2559_; lean_object* v___x_2561_; 
v_btrueExpr_2559_ = lean_ctor_get(v_a_2555_, 3);
lean_inc_ref(v_btrueExpr_2559_);
lean_dec(v_a_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_btrueExpr_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_btrueExpr_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2564_);
lean_dec_ref(v_a_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2567_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2598_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
size_t v___x_2591_; size_t v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2591_ = lean_ptr_addr(v_e_2583_);
v___x_2592_ = lean_ptr_addr(v_a_2587_);
lean_dec(v_a_2587_);
v___x_2593_ = lean_usize_dec_eq(v___x_2591_, v___x_2592_);
v___x_2594_ = lean_box(v___x_2593_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2594_);
v___x_2596_ = v___x_2589_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
v_a_2599_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2586_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2586_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2607_, v_a_2608_);
lean_dec_ref(v_a_2608_);
lean_dec_ref(v_e_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2611_, v_a_2612_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_e_2620_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2640_; 
v___x_2631_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2629_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_bfalseExpr_2636_; lean_object* v___x_2638_; 
v_bfalseExpr_2636_ = lean_ctor_get(v_a_2632_, 4);
lean_inc_ref(v_bfalseExpr_2636_);
lean_dec(v_a_2632_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_bfalseExpr_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_bfalseExpr_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2641_);
lean_dec_ref(v_a_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2644_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2675_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2675_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2675_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
size_t v___x_2668_; size_t v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2668_ = lean_ptr_addr(v_e_2660_);
v___x_2669_ = lean_ptr_addr(v_a_2664_);
lean_dec(v_a_2664_);
v___x_2670_ = lean_usize_dec_eq(v___x_2668_, v___x_2669_);
v___x_2671_ = lean_box(v___x_2670_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2671_);
v___x_2673_ = v___x_2666_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2663_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2663_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2684_, v_a_2685_);
lean_dec_ref(v_a_2685_);
lean_dec_ref(v_e_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2688_, v_a_2689_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec_ref(v_e_2697_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2708_; lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2717_; 
v___x_2708_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2706_);
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2717_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2717_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_natZExpr_2713_; lean_object* v___x_2715_; 
v_natZExpr_2713_ = lean_ctor_get(v_a_2709_, 2);
lean_inc_ref(v_natZExpr_2713_);
lean_dec(v_a_2709_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v_natZExpr_2713_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_natZExpr_2713_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2718_);
lean_dec_ref(v_a_2718_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2721_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2739_; lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2748_; 
v___x_2739_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2737_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v_ordEqExpr_2744_; lean_object* v___x_2746_; 
v_ordEqExpr_2744_ = lean_ctor_get(v_a_2740_, 5);
lean_inc_ref(v_ordEqExpr_2744_);
lean_dec(v_a_2740_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v_ordEqExpr_2744_);
v___x_2746_ = v___x_2742_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_ordEqExpr_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2749_);
lean_dec_ref(v_a_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2752_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v___x_2770_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2768_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_intExpr_2775_; lean_object* v___x_2777_; 
v_intExpr_2775_ = lean_ctor_get(v_a_2771_, 6);
lean_inc_ref(v_intExpr_2775_);
lean_dec(v_a_2771_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v_intExpr_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_intExpr_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2780_);
lean_dec_ref(v_a_2780_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2783_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Meta_Sym_getIntExpr(v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2799_, lean_object* v_ctx_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2803_; lean_object* v_share_2804_; lean_object* v_maxFVar_2805_; lean_object* v_proofInstInfo_2806_; lean_object* v_proofInstInfoFVar_2807_; lean_object* v_letValue_2808_; lean_object* v_inferType_2809_; lean_object* v_getLevel_2810_; lean_object* v_congrInfo_2811_; lean_object* v_defEqI_2812_; lean_object* v_extensions_2813_; lean_object* v_issues_2814_; lean_object* v_canon_2815_; lean_object* v_instanceOverrides_2816_; uint8_t v_debug_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2881_; 
v___x_2803_ = lean_st_ref_take(v_a_2801_);
v_share_2804_ = lean_ctor_get(v___x_2803_, 0);
v_maxFVar_2805_ = lean_ctor_get(v___x_2803_, 1);
v_proofInstInfo_2806_ = lean_ctor_get(v___x_2803_, 2);
v_proofInstInfoFVar_2807_ = lean_ctor_get(v___x_2803_, 3);
v_letValue_2808_ = lean_ctor_get(v___x_2803_, 4);
v_inferType_2809_ = lean_ctor_get(v___x_2803_, 5);
v_getLevel_2810_ = lean_ctor_get(v___x_2803_, 6);
v_congrInfo_2811_ = lean_ctor_get(v___x_2803_, 7);
v_defEqI_2812_ = lean_ctor_get(v___x_2803_, 8);
v_extensions_2813_ = lean_ctor_get(v___x_2803_, 9);
v_issues_2814_ = lean_ctor_get(v___x_2803_, 10);
v_canon_2815_ = lean_ctor_get(v___x_2803_, 11);
v_instanceOverrides_2816_ = lean_ctor_get(v___x_2803_, 12);
v_debug_2817_ = lean_ctor_get_uint8(v___x_2803_, sizeof(void*)*13);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2819_ = v___x_2803_;
v_isShared_2820_ = v_isSharedCheck_2881_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_instanceOverrides_2816_);
lean_inc(v_canon_2815_);
lean_inc(v_issues_2814_);
lean_inc(v_extensions_2813_);
lean_inc(v_defEqI_2812_);
lean_inc(v_congrInfo_2811_);
lean_inc(v_getLevel_2810_);
lean_inc(v_inferType_2809_);
lean_inc(v_letValue_2808_);
lean_inc(v_proofInstInfoFVar_2807_);
lean_inc(v_proofInstInfo_2806_);
lean_inc(v_maxFVar_2805_);
lean_inc(v_share_2804_);
lean_dec(v___x_2803_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2881_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2821_);
v___x_2823_ = v___x_2819_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_maxFVar_2805_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_proofInstInfo_2806_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_proofInstInfoFVar_2807_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_letValue_2808_);
lean_ctor_set(v_reuseFailAlloc_2880_, 5, v_inferType_2809_);
lean_ctor_set(v_reuseFailAlloc_2880_, 6, v_getLevel_2810_);
lean_ctor_set(v_reuseFailAlloc_2880_, 7, v_congrInfo_2811_);
lean_ctor_set(v_reuseFailAlloc_2880_, 8, v_defEqI_2812_);
lean_ctor_set(v_reuseFailAlloc_2880_, 9, v_extensions_2813_);
lean_ctor_set(v_reuseFailAlloc_2880_, 10, v_issues_2814_);
lean_ctor_set(v_reuseFailAlloc_2880_, 11, v_canon_2815_);
lean_ctor_set(v_reuseFailAlloc_2880_, 12, v_instanceOverrides_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*13, v_debug_2817_);
v___x_2823_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_st_ref_put(v_a_2801_, v___x_2823_);
v___x_2825_ = lean_apply_2(v_k_2799_, v_ctx_2800_, v_share_2804_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v_maxFVar_2829_; lean_object* v_proofInstInfo_2830_; lean_object* v_proofInstInfoFVar_2831_; lean_object* v_letValue_2832_; lean_object* v_inferType_2833_; lean_object* v_getLevel_2834_; lean_object* v_congrInfo_2835_; lean_object* v_defEqI_2836_; lean_object* v_extensions_2837_; lean_object* v_issues_2838_; lean_object* v_canon_2839_; lean_object* v_instanceOverrides_2840_; uint8_t v_debug_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2851_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
v_a_2827_ = lean_ctor_get(v___x_2825_, 1);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2825_, 2);
v___x_2828_ = lean_st_ref_take(v_a_2801_);
v_maxFVar_2829_ = lean_ctor_get(v___x_2828_, 1);
v_proofInstInfo_2830_ = lean_ctor_get(v___x_2828_, 2);
v_proofInstInfoFVar_2831_ = lean_ctor_get(v___x_2828_, 3);
v_letValue_2832_ = lean_ctor_get(v___x_2828_, 4);
v_inferType_2833_ = lean_ctor_get(v___x_2828_, 5);
v_getLevel_2834_ = lean_ctor_get(v___x_2828_, 6);
v_congrInfo_2835_ = lean_ctor_get(v___x_2828_, 7);
v_defEqI_2836_ = lean_ctor_get(v___x_2828_, 8);
v_extensions_2837_ = lean_ctor_get(v___x_2828_, 9);
v_issues_2838_ = lean_ctor_get(v___x_2828_, 10);
v_canon_2839_ = lean_ctor_get(v___x_2828_, 11);
v_instanceOverrides_2840_ = lean_ctor_get(v___x_2828_, 12);
v_debug_2841_ = lean_ctor_get_uint8(v___x_2828_, sizeof(void*)*13);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2852_);
v___x_2843_ = v___x_2828_;
v_isShared_2844_ = v_isSharedCheck_2851_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_instanceOverrides_2840_);
lean_inc(v_canon_2839_);
lean_inc(v_issues_2838_);
lean_inc(v_extensions_2837_);
lean_inc(v_defEqI_2836_);
lean_inc(v_congrInfo_2835_);
lean_inc(v_getLevel_2834_);
lean_inc(v_inferType_2833_);
lean_inc(v_letValue_2832_);
lean_inc(v_proofInstInfoFVar_2831_);
lean_inc(v_proofInstInfo_2830_);
lean_inc(v_maxFVar_2829_);
lean_dec(v___x_2828_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2851_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_a_2827_);
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2827_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_maxFVar_2829_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_proofInstInfo_2830_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_proofInstInfoFVar_2831_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_letValue_2832_);
lean_ctor_set(v_reuseFailAlloc_2850_, 5, v_inferType_2833_);
lean_ctor_set(v_reuseFailAlloc_2850_, 6, v_getLevel_2834_);
lean_ctor_set(v_reuseFailAlloc_2850_, 7, v_congrInfo_2835_);
lean_ctor_set(v_reuseFailAlloc_2850_, 8, v_defEqI_2836_);
lean_ctor_set(v_reuseFailAlloc_2850_, 9, v_extensions_2837_);
lean_ctor_set(v_reuseFailAlloc_2850_, 10, v_issues_2838_);
lean_ctor_set(v_reuseFailAlloc_2850_, 11, v_canon_2839_);
lean_ctor_set(v_reuseFailAlloc_2850_, 12, v_instanceOverrides_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, sizeof(void*)*13, v_debug_2841_);
v___x_2846_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_st_ref_put(v_a_2801_, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_a_2826_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v_maxFVar_2856_; lean_object* v_proofInstInfo_2857_; lean_object* v_proofInstInfoFVar_2858_; lean_object* v_letValue_2859_; lean_object* v_inferType_2860_; lean_object* v_getLevel_2861_; lean_object* v_congrInfo_2862_; lean_object* v_defEqI_2863_; lean_object* v_extensions_2864_; lean_object* v_issues_2865_; lean_object* v_canon_2866_; lean_object* v_instanceOverrides_2867_; uint8_t v_debug_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2878_; 
v_a_2853_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2853_);
v_a_2854_ = lean_ctor_get(v___x_2825_, 1);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2825_, 2);
v___x_2855_ = lean_st_ref_take(v_a_2801_);
v_maxFVar_2856_ = lean_ctor_get(v___x_2855_, 1);
v_proofInstInfo_2857_ = lean_ctor_get(v___x_2855_, 2);
v_proofInstInfoFVar_2858_ = lean_ctor_get(v___x_2855_, 3);
v_letValue_2859_ = lean_ctor_get(v___x_2855_, 4);
v_inferType_2860_ = lean_ctor_get(v___x_2855_, 5);
v_getLevel_2861_ = lean_ctor_get(v___x_2855_, 6);
v_congrInfo_2862_ = lean_ctor_get(v___x_2855_, 7);
v_defEqI_2863_ = lean_ctor_get(v___x_2855_, 8);
v_extensions_2864_ = lean_ctor_get(v___x_2855_, 9);
v_issues_2865_ = lean_ctor_get(v___x_2855_, 10);
v_canon_2866_ = lean_ctor_get(v___x_2855_, 11);
v_instanceOverrides_2867_ = lean_ctor_get(v___x_2855_, 12);
v_debug_2868_ = lean_ctor_get_uint8(v___x_2855_, sizeof(void*)*13);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v___x_2855_, 0);
lean_dec(v_unused_2879_);
v___x_2870_ = v___x_2855_;
v_isShared_2871_ = v_isSharedCheck_2878_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_instanceOverrides_2867_);
lean_inc(v_canon_2866_);
lean_inc(v_issues_2865_);
lean_inc(v_extensions_2864_);
lean_inc(v_defEqI_2863_);
lean_inc(v_congrInfo_2862_);
lean_inc(v_getLevel_2861_);
lean_inc(v_inferType_2860_);
lean_inc(v_letValue_2859_);
lean_inc(v_proofInstInfoFVar_2858_);
lean_inc(v_proofInstInfo_2857_);
lean_inc(v_maxFVar_2856_);
lean_dec(v___x_2855_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2878_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v_a_2854_);
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2854_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_maxFVar_2856_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_proofInstInfo_2857_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_proofInstInfoFVar_2858_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_letValue_2859_);
lean_ctor_set(v_reuseFailAlloc_2877_, 5, v_inferType_2860_);
lean_ctor_set(v_reuseFailAlloc_2877_, 6, v_getLevel_2861_);
lean_ctor_set(v_reuseFailAlloc_2877_, 7, v_congrInfo_2862_);
lean_ctor_set(v_reuseFailAlloc_2877_, 8, v_defEqI_2863_);
lean_ctor_set(v_reuseFailAlloc_2877_, 9, v_extensions_2864_);
lean_ctor_set(v_reuseFailAlloc_2877_, 10, v_issues_2865_);
lean_ctor_set(v_reuseFailAlloc_2877_, 11, v_canon_2866_);
lean_ctor_set(v_reuseFailAlloc_2877_, 12, v_instanceOverrides_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*13, v_debug_2868_);
v___x_2873_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_st_ref_put(v_a_2801_, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_a_2853_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2882_, lean_object* v_ctx_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2882_, v_ctx_2883_, v_a_2884_);
lean_dec(v_a_2884_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2887_, lean_object* v_k_2888_, lean_object* v_ctx_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2888_, v_ctx_2889_, v_a_2891_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_k_2899_, lean_object* v_ctx_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2898_, v_k_2899_, v_ctx_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2909_){
_start:
{
lean_object* v_config_2910_; lean_object* v_sharedExprs_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2928_; 
v_config_2910_ = lean_ctor_get(v_ctx_2909_, 1);
v_sharedExprs_2911_ = lean_ctor_get(v_ctx_2909_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_ctx_2909_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2913_ = v_ctx_2909_;
v_isShared_2914_ = v_isSharedCheck_2928_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_config_2910_);
lean_inc(v_sharedExprs_2911_);
lean_dec(v_ctx_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2928_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v_verbose_2915_; uint8_t v_enforceUnfoldReducible_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2927_; 
v_verbose_2915_ = lean_ctor_get_uint8(v_config_2910_, 0);
v_enforceUnfoldReducible_2916_ = lean_ctor_get_uint8(v_config_2910_, 1);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_config_2910_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2918_ = v_config_2910_;
v_isShared_2919_ = v_isSharedCheck_2927_;
goto v_resetjp_2917_;
}
else
{
lean_dec(v_config_2910_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2927_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
uint8_t v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = 0;
if (v_isShared_2919_ == 0)
{
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 0, v_verbose_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 1, v_enforceUnfoldReducible_2916_);
v___x_2922_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
lean_ctor_set_uint8(v___x_2922_, 2, v___x_2920_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2922_);
v___x_2924_ = v___x_2913_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_sharedExprs_2911_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v___f_2932_; lean_object* v___x_2933_; 
v___f_2932_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2933_ = lean_apply_3(v_inst_2930_, lean_box(0), v___f_2932_, v_x_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2934_, lean_object* v_00_u03b1_2935_, lean_object* v_inst_2936_, lean_object* v_x_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2936_, v_x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2939_){
_start:
{
lean_object* v_config_2940_; lean_object* v_sharedExprs_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2957_; 
v_config_2940_ = lean_ctor_get(v_ctx_2939_, 1);
v_sharedExprs_2941_ = lean_ctor_get(v_ctx_2939_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_ctx_2939_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2943_ = v_ctx_2939_;
v_isShared_2944_ = v_isSharedCheck_2957_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_config_2940_);
lean_inc(v_sharedExprs_2941_);
lean_dec(v_ctx_2939_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2957_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
uint8_t v_verbose_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2956_; 
v_verbose_2945_ = lean_ctor_get_uint8(v_config_2940_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_config_2940_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2947_ = v_config_2940_;
v_isShared_2948_ = v_isSharedCheck_2956_;
goto v_resetjp_2946_;
}
else
{
lean_dec(v_config_2940_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2956_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
uint8_t v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = 0;
if (v_isShared_2948_ == 0)
{
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, 0, v_verbose_2945_);
v___x_2951_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
lean_ctor_set_uint8(v___x_2951_, 1, v___x_2949_);
lean_ctor_set_uint8(v___x_2951_, 2, v___x_2949_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_2951_);
v___x_2953_ = v___x_2943_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_sharedExprs_2941_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_2959_, lean_object* v_x_2960_){
_start:
{
lean_object* v___f_2961_; lean_object* v___x_2962_; 
v___f_2961_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_2962_ = lean_apply_3(v_inst_2959_, lean_box(0), v___f_2961_, v_x_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_2963_, lean_object* v_00_u03b1_2964_, lean_object* v_inst_2965_, lean_object* v_x_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_2965_, v_x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_config_2971_; lean_object* v___x_2972_; lean_object* v_env_2973_; uint8_t v_enforceUnfoldReducible_2974_; uint8_t v_enforceFoldProjs_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_config_2971_ = lean_ctor_get(v_a_2968_, 1);
v___x_2972_ = lean_st_ref_get(v_a_2969_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc_ref(v_env_2973_);
lean_dec(v___x_2972_);
v_enforceUnfoldReducible_2974_ = lean_ctor_get_uint8(v_config_2971_, 1);
v_enforceFoldProjs_2975_ = lean_ctor_get_uint8(v_config_2971_, 2);
v___x_2976_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2976_, 0, v_env_2973_);
lean_ctor_set_uint8(v___x_2976_, sizeof(void*)*1, v_enforceUnfoldReducible_2974_);
lean_ctor_set_uint8(v___x_2976_, sizeof(void*)*1 + 1, v_enforceFoldProjs_2975_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2978_, v_a_2979_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2982_, v_a_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_config_3005_; uint8_t v_enforceUnfoldReducible_3006_; uint8_t v_enforceFoldProjs_3007_; lean_object* v_e_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v_e_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; 
v_config_3005_ = lean_ctor_get(v_a_2999_, 1);
v_enforceUnfoldReducible_3006_ = lean_ctor_get_uint8(v_config_3005_, 1);
v_enforceFoldProjs_3007_ = lean_ctor_get_uint8(v_config_3005_, 2);
if (v_enforceUnfoldReducible_3006_ == 0)
{
v_e_3017_ = v_e_2998_;
v___y_3018_ = v_a_3000_;
v___y_3019_ = v_a_3001_;
v___y_3020_ = v_a_3002_;
v___y_3021_ = v_a_3003_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Meta_Sym_unfoldReducible(v_e_2998_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v_e_3017_ = v_a_3025_;
v___y_3018_ = v_a_3000_;
v___y_3019_ = v_a_3001_;
v___y_3020_ = v_a_3002_;
v___y_3021_ = v_a_3003_;
goto v___jp_3016_;
}
else
{
return v___x_3024_;
}
}
v___jp_3008_:
{
if (v_enforceUnfoldReducible_3006_ == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_e_3009_);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3015_;
}
}
v___jp_3016_:
{
if (v_enforceFoldProjs_3007_ == 0)
{
v_e_3009_ = v_e_3017_;
v___y_3010_ = v___y_3018_;
v___y_3011_ = v___y_3019_;
v___y_3012_ = v___y_3020_;
v___y_3013_ = v___y_3021_;
goto v___jp_3008_;
}
else
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Meta_Sym_foldProjs(v_e_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_e_3009_ = v_a_3023_;
v___y_3010_ = v___y_3018_;
v___y_3011_ = v___y_3019_;
v___y_3012_ = v___y_3020_;
v___y_3013_ = v___y_3021_;
goto v___jp_3008_;
}
else
{
return v___x_3022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec_ref(v_a_3027_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3034_, v_a_3035_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
return v_res_3051_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_instMonadEIO___redArg();
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_toApplicative_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3130_; 
v___x_3065_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3066_ = l_StateRefT_x27_instMonad___redArg(v___x_3065_);
v_toApplicative_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v___x_3066_, 1);
lean_dec(v_unused_3131_);
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3130_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_toApplicative_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3130_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_toFunctor_3071_; lean_object* v_toSeq_3072_; lean_object* v_toSeqLeft_3073_; lean_object* v_toSeqRight_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3128_; 
v_toFunctor_3071_ = lean_ctor_get(v_toApplicative_3067_, 0);
v_toSeq_3072_ = lean_ctor_get(v_toApplicative_3067_, 2);
v_toSeqLeft_3073_ = lean_ctor_get(v_toApplicative_3067_, 3);
v_toSeqRight_3074_ = lean_ctor_get(v_toApplicative_3067_, 4);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_toApplicative_3067_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; 
v_unused_3129_ = lean_ctor_get(v_toApplicative_3067_, 1);
lean_dec(v_unused_3129_);
v___x_3076_ = v_toApplicative_3067_;
v_isShared_3077_ = v_isSharedCheck_3128_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_toSeqRight_3074_);
lean_inc(v_toSeqLeft_3073_);
lean_inc(v_toSeq_3072_);
lean_inc(v_toFunctor_3071_);
lean_dec(v_toApplicative_3067_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3128_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___x_3087_; 
v___f_3078_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3079_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3071_);
v___f_3080_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3080_, 0, v_toFunctor_3071_);
v___f_3081_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3081_, 0, v_toFunctor_3071_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___f_3080_);
lean_ctor_set(v___x_3082_, 1, v___f_3081_);
v___f_3083_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3083_, 0, v_toSeqRight_3074_);
v___f_3084_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3084_, 0, v_toSeqLeft_3073_);
v___f_3085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3085_, 0, v_toSeq_3072_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___f_3083_);
lean_ctor_set(v___x_3076_, 3, v___f_3084_);
lean_ctor_set(v___x_3076_, 2, v___f_3085_);
lean_ctor_set(v___x_3076_, 1, v___f_3078_);
lean_ctor_set(v___x_3076_, 0, v___x_3082_);
v___x_3087_ = v___x_3076_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___f_3078_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v___f_3085_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v___f_3084_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v___f_3083_);
v___x_3087_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3089_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v___f_3079_);
lean_ctor_set(v___x_3069_, 0, v___x_3087_);
v___x_3089_ = v___x_3069_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___f_3079_);
v___x_3089_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v_toApplicative_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3124_; 
v___x_3090_ = l_StateRefT_x27_instMonad___redArg(v___x_3089_);
v_toApplicative_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v___x_3090_, 1);
lean_dec(v_unused_3125_);
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3124_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_toApplicative_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3124_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_toFunctor_3095_; lean_object* v_toSeq_3096_; lean_object* v_toSeqLeft_3097_; lean_object* v_toSeqRight_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3122_; 
v_toFunctor_3095_ = lean_ctor_get(v_toApplicative_3091_, 0);
v_toSeq_3096_ = lean_ctor_get(v_toApplicative_3091_, 2);
v_toSeqLeft_3097_ = lean_ctor_get(v_toApplicative_3091_, 3);
v_toSeqRight_3098_ = lean_ctor_get(v_toApplicative_3091_, 4);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_toApplicative_3091_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v_toApplicative_3091_, 1);
lean_dec(v_unused_3123_);
v___x_3100_ = v_toApplicative_3091_;
v_isShared_3101_ = v_isSharedCheck_3122_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_toSeqRight_3098_);
lean_inc(v_toSeqLeft_3097_);
lean_inc(v_toSeq_3096_);
lean_inc(v_toFunctor_3095_);
lean_dec(v_toApplicative_3091_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3122_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___f_3102_; lean_object* v___f_3103_; lean_object* v___f_3104_; lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___x_3111_; 
v___f_3102_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3103_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3095_);
v___f_3104_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3104_, 0, v_toFunctor_3095_);
v___f_3105_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3105_, 0, v_toFunctor_3095_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___f_3104_);
lean_ctor_set(v___x_3106_, 1, v___f_3105_);
v___f_3107_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3107_, 0, v_toSeqRight_3098_);
v___f_3108_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3108_, 0, v_toSeqLeft_3097_);
v___f_3109_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3109_, 0, v_toSeq_3096_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___f_3107_);
lean_ctor_set(v___x_3100_, 3, v___f_3108_);
lean_ctor_set(v___x_3100_, 2, v___f_3109_);
lean_ctor_set(v___x_3100_, 1, v___f_3102_);
lean_ctor_set(v___x_3100_, 0, v___x_3106_);
v___x_3111_ = v___x_3100_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___f_3102_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v___f_3109_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v___f_3108_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v___f_3107_);
v___x_3111_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 1, v___f_3103_);
lean_ctor_set(v___x_3093_, 0, v___x_3111_);
v___x_3113_ = v___x_3093_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___f_3103_);
v___x_3113_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___f_3117_; lean_object* v___x_925__overap_3118_; lean_object* v___x_3119_; 
v___x_3114_ = l_StateRefT_x27_instMonad___redArg(v___x_3113_);
v___x_3115_ = l_Lean_instInhabitedExpr;
v___x_3116_ = l_instInhabitedOfMonad___redArg(v___x_3114_, v___x_3115_);
v___f_3117_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3117_, 0, v___x_3116_);
v___x_925__overap_3118_ = lean_panic_fn_borrowed(v___f_3117_, v_msg_3057_);
lean_dec_ref(v___f_3117_);
lean_inc(v___y_3063_);
lean_inc_ref(v___y_3062_);
lean_inc(v___y_3061_);
lean_inc_ref(v___y_3060_);
lean_inc(v___y_3059_);
lean_inc_ref(v___y_3058_);
v___x_3119_ = lean_apply_7(v___x_925__overap_3118_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, lean_box(0));
return v___x_3119_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3141_, lean_object* v_vals_3142_, lean_object* v_i_3143_, lean_object* v_k_3144_){
_start:
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = lean_array_get_size(v_keys_3141_);
v___x_3146_ = lean_nat_dec_lt(v_i_3143_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v_i_3143_);
v___x_3147_ = lean_box(0);
return v___x_3147_;
}
else
{
lean_object* v_k_x27_3148_; uint8_t v___x_3149_; 
v_k_x27_3148_ = lean_array_fget_borrowed(v_keys_3141_, v_i_3143_);
v___x_3149_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3144_, v_k_x27_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_unsigned_to_nat(1u);
v___x_3151_ = lean_nat_add(v_i_3143_, v___x_3150_);
lean_dec(v_i_3143_);
v_i_3143_ = v___x_3151_;
goto _start;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = lean_array_fget_borrowed(v_vals_3142_, v_i_3143_);
lean_dec(v_i_3143_);
lean_inc(v___x_3153_);
lean_inc(v_k_x27_3148_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_k_x27_3148_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3156_, lean_object* v_vals_3157_, lean_object* v_i_3158_, lean_object* v_k_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3156_, v_vals_3157_, v_i_3158_, v_k_3159_);
lean_dec_ref(v_k_3159_);
lean_dec_ref(v_vals_3157_);
lean_dec_ref(v_keys_3156_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3161_, size_t v_x_3162_, lean_object* v_x_3163_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
lean_object* v_es_3164_; lean_object* v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; lean_object* v_j_3168_; lean_object* v___x_3169_; 
v_es_3164_ = lean_ctor_get(v_x_3161_, 0);
v___x_3165_ = lean_box(2);
v___x_3166_ = ((size_t)31ULL);
v___x_3167_ = lean_usize_land(v_x_3162_, v___x_3166_);
v_j_3168_ = lean_usize_to_nat(v___x_3167_);
v___x_3169_ = lean_array_get_borrowed(v___x_3165_, v_es_3164_, v_j_3168_);
lean_dec(v_j_3168_);
switch(lean_obj_tag(v___x_3169_))
{
case 0:
{
lean_object* v_key_3170_; lean_object* v_val_3171_; uint8_t v___x_3172_; 
v_key_3170_ = lean_ctor_get(v___x_3169_, 0);
v_val_3171_ = lean_ctor_get(v___x_3169_, 1);
v___x_3172_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3163_, v_key_3170_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_box(0);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_inc(v_val_3171_);
lean_inc(v_key_3170_);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_key_3170_);
lean_ctor_set(v___x_3174_, 1, v_val_3171_);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
case 1:
{
lean_object* v_node_3176_; size_t v___x_3177_; size_t v___x_3178_; 
v_node_3176_ = lean_ctor_get(v___x_3169_, 0);
v___x_3177_ = ((size_t)5ULL);
v___x_3178_ = lean_usize_shift_right(v_x_3162_, v___x_3177_);
v_x_3161_ = v_node_3176_;
v_x_3162_ = v___x_3178_;
goto _start;
}
default: 
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_box(0);
return v___x_3180_;
}
}
}
else
{
lean_object* v_ks_3181_; lean_object* v_vs_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_ks_3181_ = lean_ctor_get(v_x_3161_, 0);
v_vs_3182_ = lean_ctor_get(v_x_3161_, 1);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3181_, v_vs_3182_, v___x_3183_, v_x_3163_);
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3185_, lean_object* v_x_3186_, lean_object* v_x_3187_){
_start:
{
size_t v_x_1247__boxed_3188_; lean_object* v_res_3189_; 
v_x_1247__boxed_3188_ = lean_unbox_usize(v_x_3186_);
lean_dec(v_x_3186_);
v_res_3189_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3185_, v_x_1247__boxed_3188_, v_x_3187_);
lean_dec_ref(v_x_3187_);
lean_dec_ref(v_x_3185_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
uint64_t v___x_3192_; size_t v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3191_);
v___x_3193_ = lean_uint64_to_usize(v___x_3192_);
v___x_3194_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3190_, v___x_3193_, v_x_3191_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3195_, v_x_3196_);
lean_dec_ref(v_x_3196_);
lean_dec_ref(v_x_3195_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3198_, lean_object* v_cache_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3201_, v_e_3198_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_cache_3199_);
lean_ctor_set(v___x_3203_, 1, v___y_3201_);
v___x_3204_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3198_, v___y_3200_, v___x_3203_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3214_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 1);
v_a_3206_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3208_ = v___x_3204_;
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3205_);
lean_inc(v_a_3206_);
lean_dec(v___x_3204_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_set_3210_; lean_object* v___x_3212_; 
v_set_3210_ = lean_ctor_get(v_a_3205_, 1);
lean_inc_ref(v_set_3210_);
lean_dec(v_a_3205_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v_set_3210_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3206_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_set_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3224_; 
v_a_3215_ = lean_ctor_get(v___x_3204_, 1);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; 
v_unused_3225_ = lean_ctor_get(v___x_3204_, 0);
lean_dec(v_unused_3225_);
v___x_3217_ = v___x_3204_;
v_isShared_3218_ = v_isSharedCheck_3224_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3204_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3224_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v_map_3219_; lean_object* v_set_3220_; lean_object* v___x_3222_; 
v_map_3219_ = lean_ctor_get(v_a_3215_, 0);
lean_inc_ref(v_map_3219_);
v_set_3220_ = lean_ctor_get(v_a_3215_, 1);
lean_inc_ref(v_set_3220_);
lean_dec(v_a_3215_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 1, v_set_3220_);
lean_ctor_set(v___x_3217_, 0, v_map_3219_);
v___x_3222_ = v___x_3217_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_map_3219_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_set_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_val_3226_; lean_object* v_fst_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v_cache_3199_);
lean_dec_ref(v_e_3198_);
v_val_3226_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_val_3226_);
lean_dec_ref_known(v___x_3202_, 1);
v_fst_3227_ = lean_ctor_get(v_val_3226_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_val_3226_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v_val_3226_, 1);
lean_dec(v_unused_3235_);
v___x_3229_ = v_val_3226_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_fst_3227_);
lean_dec(v_val_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 1, v___y_3201_);
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_fst_3227_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___y_3201_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3236_, lean_object* v_cache_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3236_, v_cache_3237_, v___y_3238_, v___y_3239_);
lean_dec_ref(v___y_3238_);
return v_res_3240_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3242_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3243_ = lean_unsigned_to_nat(16u);
v___x_3244_ = lean_unsigned_to_nat(401u);
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3246_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_3247_ = l_mkPanicMessageWithDecl(v___x_3246_, v___x_3245_, v___x_3244_, v___x_3243_, v___x_3242_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3248_, lean_object* v_cache_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v___f_3257_; lean_object* v___x_3258_; lean_object* v_env_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3273_; 
v___f_3257_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3257_, 0, v_e_3248_);
lean_closure_set(v___f_3257_, 1, v_cache_3249_);
v___x_3258_ = lean_st_ref_get(v_a_3255_);
v_env_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_ref(v_env_3259_);
lean_dec(v___x_3258_);
v___x_3260_ = 0;
v___x_3261_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3261_, 0, v_env_3259_);
lean_ctor_set_uint8(v___x_3261_, sizeof(void*)*1, v___x_3260_);
lean_ctor_set_uint8(v___x_3261_, sizeof(void*)*1 + 1, v___x_3260_);
v___x_3262_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3257_, v___x_3261_, v_a_3251_);
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3273_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3273_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
if (lean_obj_tag(v_a_3263_) == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec_ref_known(v_a_3263_, 1);
lean_del_object(v___x_3265_);
v___x_3267_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3268_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3267_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
return v___x_3268_;
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; 
v_a_3269_ = lean_ctor_get(v_a_3263_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v_a_3263_, 1);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v_a_3269_);
v___x_3271_ = v___x_3265_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3274_, lean_object* v_cache_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3274_, v_cache_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3288_, v_x_3289_, v_x_3290_);
lean_dec_ref(v_x_3290_);
lean_dec_ref(v_x_3289_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3292_, lean_object* v_x_3293_, size_t v_x_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3293_, v_x_3294_, v_x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
size_t v_x_1452__boxed_3301_; lean_object* v_res_3302_; 
v_x_1452__boxed_3301_ = lean_unbox_usize(v_x_3299_);
lean_dec(v_x_3299_);
v_res_3302_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3297_, v_x_3298_, v_x_1452__boxed_3301_, v_x_3300_);
lean_dec_ref(v_x_3300_);
lean_dec_ref(v_x_3298_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3303_, lean_object* v_keys_3304_, lean_object* v_vals_3305_, lean_object* v_heq_3306_, lean_object* v_i_3307_, lean_object* v_k_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3304_, v_vals_3305_, v_i_3307_, v_k_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3310_, lean_object* v_keys_3311_, lean_object* v_vals_3312_, lean_object* v_heq_3313_, lean_object* v_i_3314_, lean_object* v_k_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3310_, v_keys_3311_, v_vals_3312_, v_heq_3313_, v_i_3314_, v_k_3315_);
lean_dec_ref(v_k_3315_);
lean_dec_ref(v_vals_3312_);
lean_dec_ref(v_keys_3311_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg(lean_object* v_e_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v_share_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_st_ref_get(v_a_3318_);
v_share_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc_ref(v_share_3321_);
lean_dec(v___x_3320_);
v___x_3322_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_share_3321_, v_e_3317_);
lean_dec_ref(v_share_3321_);
if (lean_obj_tag(v___x_3322_) == 0)
{
uint8_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = 0;
v___x_3324_ = lean_box(v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
else
{
lean_object* v_val_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3338_; 
v_val_3326_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3328_ = v___x_3322_;
v_isShared_3329_ = v_isSharedCheck_3338_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_val_3326_);
lean_dec(v___x_3322_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3338_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_fst_3330_; size_t v___x_3331_; size_t v___x_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v_fst_3330_ = lean_ctor_get(v_val_3326_, 0);
lean_inc(v_fst_3330_);
lean_dec(v_val_3326_);
v___x_3331_ = lean_ptr_addr(v_fst_3330_);
lean_dec(v_fst_3330_);
v___x_3332_ = lean_ptr_addr(v_e_3317_);
v___x_3333_ = lean_usize_dec_eq(v___x_3331_, v___x_3332_);
v___x_3334_ = lean_box(v___x_3333_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set_tag(v___x_3328_, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3334_);
v___x_3336_ = v___x_3328_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg___boxed(lean_object* v_e_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_e_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_e_3339_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared(lean_object* v_e_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_e_3343_, v_a_3345_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___boxed(lean_object* v_e_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Meta_Sym_isMaxShared(v_e_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec_ref(v_e_3352_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_ref_3367_; lean_object* v___x_3368_; lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_ref_3367_ = lean_ctor_get(v___y_3364_, 2);
v___x_3368_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
lean_inc(v_ref_3367_);
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v_ref_3367_);
lean_ctor_set(v___x_3373_, 1, v_a_3369_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 1);
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
return v_res_3384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3388_, lean_object* v_cache_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___x_3407_; 
v___x_3407_ = l_Lean_Expr_hasLooseBVars(v_e_3388_);
if (v___x_3407_ == 0)
{
v___y_3398_ = v_a_3390_;
v___y_3399_ = v_a_3391_;
v___y_3400_ = v_a_3392_;
v___y_3401_ = v_a_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
goto v___jp_3397_;
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec_ref(v_cache_3389_);
v___x_3408_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3409_ = l_Lean_indentExpr(v_e_3388_);
v___x_3410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3410_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3411_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
v___jp_3397_:
{
lean_object* v___x_3404_; 
v___x_3404_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3388_, v___y_3398_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v___x_3406_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3405_, v_cache_3389_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
return v___x_3406_;
}
else
{
lean_dec_ref(v_cache_3389_);
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3420_, lean_object* v_cache_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3420_, v_cache_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
lean_dec(v_a_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3430_, lean_object* v_msg_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3431_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_msg_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3440_, v_msg_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3450_, lean_object* v___x_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3453_, v_e_3450_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3451_);
lean_ctor_set(v___x_3455_, 1, v___y_3453_);
v___x_3456_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3450_, v___y_3452_, v___x_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3466_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 1);
v_a_3458_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3460_ = v___x_3456_;
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3457_);
lean_inc(v_a_3458_);
lean_dec(v___x_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_set_3462_; lean_object* v___x_3464_; 
v_set_3462_ = lean_ctor_get(v_a_3457_, 1);
lean_inc_ref(v_set_3462_);
lean_dec(v_a_3457_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v_set_3462_);
v___x_3464_ = v___x_3460_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3458_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_set_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3476_; 
v_a_3467_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3477_);
v___x_3469_ = v___x_3456_;
v_isShared_3470_ = v_isSharedCheck_3476_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3456_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3476_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_map_3471_; lean_object* v_set_3472_; lean_object* v___x_3474_; 
v_map_3471_ = lean_ctor_get(v_a_3467_, 0);
lean_inc_ref(v_map_3471_);
v_set_3472_ = lean_ctor_get(v_a_3467_, 1);
lean_inc_ref(v_set_3472_);
lean_dec(v_a_3467_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 1, v_set_3472_);
lean_ctor_set(v___x_3469_, 0, v_map_3471_);
v___x_3474_ = v___x_3469_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_map_3471_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_set_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_val_3478_; lean_object* v_fst_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v___x_3451_);
lean_dec_ref(v_e_3450_);
v_val_3478_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v___x_3454_, 1);
v_fst_3479_ = lean_ctor_get(v_val_3478_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_val_3478_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v_val_3478_, 1);
lean_dec(v_unused_3487_);
v___x_3481_ = v_val_3478_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_fst_3479_);
lean_dec(v_val_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___y_3453_);
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_fst_3479_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___y_3453_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3488_, lean_object* v___x_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3488_, v___x_3489_, v___y_3490_, v___y_3491_);
lean_dec_ref(v___y_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v___x_3501_; lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___f_3504_; lean_object* v___x_3505_; lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3516_; 
v___x_3501_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3494_, v_a_3499_);
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3493_);
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3504_, 0, v_e_3493_);
lean_closure_set(v___f_3504_, 1, v___x_3503_);
v___x_3505_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3504_, v_a_3502_, v_a_3495_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
if (lean_obj_tag(v_a_3506_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; 
lean_del_object(v___x_3508_);
v_a_3510_ = lean_ctor_get(v_a_3506_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v_a_3506_, 1);
v___x_3511_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3493_, v_a_3510_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_3511_;
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; 
lean_dec_ref(v_e_3493_);
v_a_3512_ = lean_ctor_get(v_a_3506_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v_a_3506_, 1);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v_a_3512_);
v___x_3514_ = v___x_3508_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_Meta_Sym_shareCommon(v_e_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3526_, v___y_3527_, v___y_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3530_, v___y_3531_, v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v___f_3542_; lean_object* v___x_3543_; lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3556_; 
lean_inc_ref(v_e_3534_);
v___f_3542_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3542_, 0, v_e_3534_);
v___x_3543_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3535_, v_a_3540_);
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3542_, v_a_3544_, v_a_3536_);
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3556_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3556_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
if (lean_obj_tag(v_a_3546_) == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec_ref_known(v_a_3546_, 1);
lean_del_object(v___x_3548_);
v___x_3550_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3551_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3534_, v___x_3550_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
return v___x_3551_;
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; 
lean_dec_ref(v_e_3534_);
v_a_3552_ = lean_ctor_get(v_a_3546_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v_a_3546_, 1);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v_a_3552_);
v___x_3554_ = v___x_3548_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3566_, lean_object* v_vals_3567_, lean_object* v_i_3568_, lean_object* v_k_3569_){
_start:
{
lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = lean_array_get_size(v_keys_3566_);
v___x_3571_ = lean_nat_dec_lt(v_i_3568_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
lean_dec(v_i_3568_);
v___x_3572_ = lean_box(0);
return v___x_3572_;
}
else
{
lean_object* v_k_x27_3573_; uint8_t v___x_3574_; 
v_k_x27_3573_ = lean_array_fget_borrowed(v_keys_3566_, v_i_3568_);
v___x_3574_ = l_Lean_instBEqFVarId_beq(v_k_3569_, v_k_x27_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = lean_nat_add(v_i_3568_, v___x_3575_);
lean_dec(v_i_3568_);
v_i_3568_ = v___x_3576_;
goto _start;
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_array_fget_borrowed(v_vals_3567_, v_i_3568_);
lean_dec(v_i_3568_);
lean_inc(v___x_3578_);
v___x_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3580_, lean_object* v_vals_3581_, lean_object* v_i_3582_, lean_object* v_k_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3580_, v_vals_3581_, v_i_3582_, v_k_3583_);
lean_dec(v_k_3583_);
lean_dec_ref(v_vals_3581_);
lean_dec_ref(v_keys_3580_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(lean_object* v_x_3585_, size_t v_x_3586_, lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3585_) == 0)
{
lean_object* v_es_3588_; lean_object* v___x_3589_; size_t v___x_3590_; size_t v___x_3591_; lean_object* v_j_3592_; lean_object* v___x_3593_; 
v_es_3588_ = lean_ctor_get(v_x_3585_, 0);
v___x_3589_ = lean_box(2);
v___x_3590_ = ((size_t)31ULL);
v___x_3591_ = lean_usize_land(v_x_3586_, v___x_3590_);
v_j_3592_ = lean_usize_to_nat(v___x_3591_);
v___x_3593_ = lean_array_get_borrowed(v___x_3589_, v_es_3588_, v_j_3592_);
lean_dec(v_j_3592_);
switch(lean_obj_tag(v___x_3593_))
{
case 0:
{
lean_object* v_key_3594_; lean_object* v_val_3595_; uint8_t v___x_3596_; 
v_key_3594_ = lean_ctor_get(v___x_3593_, 0);
v_val_3595_ = lean_ctor_get(v___x_3593_, 1);
v___x_3596_ = l_Lean_instBEqFVarId_beq(v_x_3587_, v_key_3594_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_box(0);
return v___x_3597_;
}
else
{
lean_object* v___x_3598_; 
lean_inc(v_val_3595_);
v___x_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_val_3595_);
return v___x_3598_;
}
}
case 1:
{
lean_object* v_node_3599_; size_t v___x_3600_; size_t v___x_3601_; 
v_node_3599_ = lean_ctor_get(v___x_3593_, 0);
v___x_3600_ = ((size_t)5ULL);
v___x_3601_ = lean_usize_shift_right(v_x_3586_, v___x_3600_);
v_x_3585_ = v_node_3599_;
v_x_3586_ = v___x_3601_;
goto _start;
}
default: 
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_box(0);
return v___x_3603_;
}
}
}
else
{
lean_object* v_ks_3604_; lean_object* v_vs_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_ks_3604_ = lean_ctor_get(v_x_3585_, 0);
v_vs_3605_ = lean_ctor_get(v_x_3585_, 1);
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3604_, v_vs_3605_, v___x_3606_, v_x_3587_);
return v___x_3607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
size_t v_x_4130__boxed_3611_; lean_object* v_res_3612_; 
v_x_4130__boxed_3611_ = lean_unbox_usize(v_x_3609_);
lean_dec(v_x_3609_);
v_res_3612_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3608_, v_x_4130__boxed_3611_, v_x_3610_);
lean_dec(v_x_3610_);
lean_dec_ref(v_x_3608_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
uint64_t v___x_3615_; size_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = l_Lean_instHashableFVarId_hash(v_x_3614_);
v___x_3616_ = lean_uint64_to_usize(v___x_3615_);
v___x_3617_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3613_, v___x_3616_, v_x_3614_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg___boxed(lean_object* v_x_3618_, lean_object* v_x_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_x_3618_, v_x_3619_);
lean_dec(v_x_3619_);
lean_dec_ref(v_x_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v_ks_3625_; lean_object* v_vs_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3650_; 
v_ks_3625_ = lean_ctor_get(v_x_3621_, 0);
v_vs_3626_ = lean_ctor_get(v_x_3621_, 1);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_x_3621_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3628_ = v_x_3621_;
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_vs_3626_);
lean_inc(v_ks_3625_);
lean_dec(v_x_3621_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = lean_array_get_size(v_ks_3625_);
v___x_3631_ = lean_nat_dec_lt(v_x_3622_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
lean_dec(v_x_3622_);
v___x_3632_ = lean_array_push(v_ks_3625_, v_x_3623_);
v___x_3633_ = lean_array_push(v_vs_3626_, v_x_3624_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v___x_3633_);
lean_ctor_set(v___x_3628_, 0, v___x_3632_);
v___x_3635_ = v___x_3628_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
else
{
lean_object* v_k_x27_3637_; uint8_t v___x_3638_; 
v_k_x27_3637_ = lean_array_fget_borrowed(v_ks_3625_, v_x_3622_);
v___x_3638_ = l_Lean_instBEqFVarId_beq(v_x_3623_, v_k_x27_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3640_; 
if (v_isShared_3629_ == 0)
{
v___x_3640_ = v___x_3628_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_ks_3625_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_vs_3626_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_unsigned_to_nat(1u);
v___x_3642_ = lean_nat_add(v_x_3622_, v___x_3641_);
lean_dec(v_x_3622_);
v_x_3621_ = v___x_3640_;
v_x_3622_ = v___x_3642_;
goto _start;
}
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3645_ = lean_array_fset(v_ks_3625_, v_x_3622_, v_x_3623_);
v___x_3646_ = lean_array_fset(v_vs_3626_, v_x_3622_, v_x_3624_);
lean_dec(v_x_3622_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v___x_3646_);
lean_ctor_set(v___x_3628_, 0, v___x_3645_);
v___x_3648_ = v___x_3628_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_3651_, lean_object* v_k_3652_, lean_object* v_v_3653_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_unsigned_to_nat(0u);
v___x_3655_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_3651_, v___x_3654_, v_k_3652_, v_v_3653_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(lean_object* v_x_3657_, size_t v_x_3658_, size_t v_x_3659_, lean_object* v_x_3660_, lean_object* v_x_3661_){
_start:
{
if (lean_obj_tag(v_x_3657_) == 0)
{
lean_object* v_es_3662_; size_t v___x_3663_; size_t v___x_3664_; lean_object* v_j_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v_es_3662_ = lean_ctor_get(v_x_3657_, 0);
v___x_3663_ = ((size_t)31ULL);
v___x_3664_ = lean_usize_land(v_x_3658_, v___x_3663_);
v_j_3665_ = lean_usize_to_nat(v___x_3664_);
v___x_3666_ = lean_array_get_size(v_es_3662_);
v___x_3667_ = lean_nat_dec_lt(v_j_3665_, v___x_3666_);
if (v___x_3667_ == 0)
{
lean_dec(v_j_3665_);
lean_dec(v_x_3661_);
lean_dec(v_x_3660_);
return v_x_3657_;
}
else
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3706_; 
lean_inc_ref(v_es_3662_);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_x_3657_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; 
v_unused_3707_ = lean_ctor_get(v_x_3657_, 0);
lean_dec(v_unused_3707_);
v___x_3669_ = v_x_3657_;
v_isShared_3670_ = v_isSharedCheck_3706_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v_x_3657_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3706_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_v_3671_; lean_object* v___x_3672_; lean_object* v_xs_x27_3673_; lean_object* v___y_3675_; 
v_v_3671_ = lean_array_fget(v_es_3662_, v_j_3665_);
v___x_3672_ = lean_box(0);
v_xs_x27_3673_ = lean_array_fset(v_es_3662_, v_j_3665_, v___x_3672_);
switch(lean_obj_tag(v_v_3671_))
{
case 0:
{
lean_object* v_key_3680_; lean_object* v_val_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3691_; 
v_key_3680_ = lean_ctor_get(v_v_3671_, 0);
v_val_3681_ = lean_ctor_get(v_v_3671_, 1);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_v_3671_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3683_ = v_v_3671_;
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_val_3681_);
lean_inc(v_key_3680_);
lean_dec(v_v_3671_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint8_t v___x_3685_; 
v___x_3685_ = l_Lean_instBEqFVarId_beq(v_x_3660_, v_key_3680_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_del_object(v___x_3683_);
v___x_3686_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3680_, v_val_3681_, v_x_3660_, v_x_3661_);
v___x_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
v___y_3675_ = v___x_3687_;
goto v___jp_3674_;
}
else
{
lean_object* v___x_3689_; 
lean_dec(v_val_3681_);
lean_dec(v_key_3680_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 1, v_x_3661_);
lean_ctor_set(v___x_3683_, 0, v_x_3660_);
v___x_3689_ = v___x_3683_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_x_3660_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_x_3661_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
v___y_3675_ = v___x_3689_;
goto v___jp_3674_;
}
}
}
}
case 1:
{
lean_object* v_node_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3704_; 
v_node_3692_ = lean_ctor_get(v_v_3671_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_v_3671_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3694_ = v_v_3671_;
v_isShared_3695_ = v_isSharedCheck_3704_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_node_3692_);
lean_dec(v_v_3671_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3704_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
size_t v___x_3696_; size_t v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3696_ = ((size_t)5ULL);
v___x_3697_ = lean_usize_shift_right(v_x_3658_, v___x_3696_);
v___x_3698_ = ((size_t)1ULL);
v___x_3699_ = lean_usize_add(v_x_3659_, v___x_3698_);
v___x_3700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_node_3692_, v___x_3697_, v___x_3699_, v_x_3660_, v_x_3661_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3700_);
v___x_3702_ = v___x_3694_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
v___y_3675_ = v___x_3702_;
goto v___jp_3674_;
}
}
}
default: 
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v_x_3660_);
lean_ctor_set(v___x_3705_, 1, v_x_3661_);
v___y_3675_ = v___x_3705_;
goto v___jp_3674_;
}
}
v___jp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = lean_array_fset(v_xs_x27_3673_, v_j_3665_, v___y_3675_);
lean_dec(v_j_3665_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3676_);
v___x_3678_ = v___x_3669_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
else
{
lean_object* v_ks_3708_; lean_object* v_vs_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3727_; 
v_ks_3708_ = lean_ctor_get(v_x_3657_, 0);
v_vs_3709_ = lean_ctor_get(v_x_3657_, 1);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_x_3657_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3711_ = v_x_3657_;
v_isShared_3712_ = v_isSharedCheck_3727_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_vs_3709_);
lean_inc(v_ks_3708_);
lean_dec(v_x_3657_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3727_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_ks_3708_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_vs_3709_);
v___x_3714_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v_newNode_3715_; size_t v___x_3716_; uint8_t v___x_3717_; 
v_newNode_3715_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(v___x_3714_, v_x_3660_, v_x_3661_);
v___x_3716_ = ((size_t)7ULL);
v___x_3717_ = lean_usize_dec_le(v___x_3716_, v_x_3659_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3718_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3715_);
v___x_3719_ = lean_unsigned_to_nat(4u);
v___x_3720_ = lean_nat_dec_lt(v___x_3718_, v___x_3719_);
lean_dec(v___x_3718_);
if (v___x_3720_ == 0)
{
lean_object* v_ks_3721_; lean_object* v_vs_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_ks_3721_ = lean_ctor_get(v_newNode_3715_, 0);
lean_inc_ref(v_ks_3721_);
v_vs_3722_ = lean_ctor_get(v_newNode_3715_, 1);
lean_inc_ref(v_vs_3722_);
lean_dec_ref(v_newNode_3715_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0);
v___x_3725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_x_3659_, v_ks_3721_, v_vs_3722_, v___x_3723_, v___x_3724_);
lean_dec_ref(v_vs_3722_);
lean_dec_ref(v_ks_3721_);
return v___x_3725_;
}
else
{
return v_newNode_3715_;
}
}
else
{
return v_newNode_3715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_3728_, lean_object* v_keys_3729_, lean_object* v_vals_3730_, lean_object* v_i_3731_, lean_object* v_entries_3732_){
_start:
{
lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3733_ = lean_array_get_size(v_keys_3729_);
v___x_3734_ = lean_nat_dec_lt(v_i_3731_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_dec(v_i_3731_);
return v_entries_3732_;
}
else
{
lean_object* v_k_3735_; lean_object* v_v_3736_; uint64_t v___x_3737_; size_t v_h_3738_; size_t v___x_3739_; lean_object* v___x_3740_; size_t v___x_3741_; size_t v___x_3742_; size_t v___x_3743_; size_t v_h_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_k_3735_ = lean_array_fget_borrowed(v_keys_3729_, v_i_3731_);
v_v_3736_ = lean_array_fget_borrowed(v_vals_3730_, v_i_3731_);
v___x_3737_ = l_Lean_instHashableFVarId_hash(v_k_3735_);
v_h_3738_ = lean_uint64_to_usize(v___x_3737_);
v___x_3739_ = ((size_t)5ULL);
v___x_3740_ = lean_unsigned_to_nat(1u);
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_sub(v_depth_3728_, v___x_3741_);
v___x_3743_ = lean_usize_mul(v___x_3739_, v___x_3742_);
v_h_3744_ = lean_usize_shift_right(v_h_3738_, v___x_3743_);
v___x_3745_ = lean_nat_add(v_i_3731_, v___x_3740_);
lean_dec(v_i_3731_);
lean_inc(v_v_3736_);
lean_inc(v_k_3735_);
v___x_3746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_entries_3732_, v_h_3744_, v_depth_3728_, v_k_3735_, v_v_3736_);
v_i_3731_ = v___x_3745_;
v_entries_3732_ = v___x_3746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_3748_, lean_object* v_keys_3749_, lean_object* v_vals_3750_, lean_object* v_i_3751_, lean_object* v_entries_3752_){
_start:
{
size_t v_depth_boxed_3753_; lean_object* v_res_3754_; 
v_depth_boxed_3753_ = lean_unbox_usize(v_depth_3748_);
lean_dec(v_depth_3748_);
v_res_3754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_3753_, v_keys_3749_, v_vals_3750_, v_i_3751_, v_entries_3752_);
lean_dec_ref(v_vals_3750_);
lean_dec_ref(v_keys_3749_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_3755_, lean_object* v_x_3756_, lean_object* v_x_3757_, lean_object* v_x_3758_, lean_object* v_x_3759_){
_start:
{
size_t v_x_4265__boxed_3760_; size_t v_x_4266__boxed_3761_; lean_object* v_res_3762_; 
v_x_4265__boxed_3760_ = lean_unbox_usize(v_x_3756_);
lean_dec(v_x_3756_);
v_x_4266__boxed_3761_ = lean_unbox_usize(v_x_3757_);
lean_dec(v_x_3757_);
v_res_3762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3755_, v_x_4265__boxed_3760_, v_x_4266__boxed_3761_, v_x_3758_, v_x_3759_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(lean_object* v_x_3763_, lean_object* v_x_3764_, lean_object* v_x_3765_){
_start:
{
uint64_t v___x_3766_; size_t v___x_3767_; size_t v___x_3768_; lean_object* v___x_3769_; 
v___x_3766_ = l_Lean_instHashableFVarId_hash(v_x_3764_);
v___x_3767_ = lean_uint64_to_usize(v___x_3766_);
v___x_3768_ = ((size_t)1ULL);
v___x_3769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3763_, v___x_3767_, v___x_3768_, v_x_3764_, v_x_3765_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f(lean_object* v_fvarId_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
uint8_t v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = 0;
lean_inc(v_fvarId_3770_);
v___x_3779_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_3770_, v___x_3778_, v_a_3773_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3854_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3854_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3854_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
if (lean_obj_tag(v_a_3780_) == 1)
{
lean_object* v_val_3784_; lean_object* v___x_3785_; lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3849_; 
lean_del_object(v___x_3782_);
v_val_3784_ = lean_ctor_get(v_a_3780_, 0);
v___x_3785_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_val_3784_, v_a_3772_);
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3849_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3849_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
uint8_t v___x_3790_; 
v___x_3790_ = lean_unbox(v_a_3786_);
lean_dec(v_a_3786_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3844_; 
lean_inc(v_val_3784_);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_a_3780_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v_a_3780_, 0);
lean_dec(v_unused_3845_);
v___x_3792_ = v_a_3780_;
v_isShared_3793_ = v_isSharedCheck_3844_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v_a_3780_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3844_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; lean_object* v_letValue_3795_; lean_object* v___x_3796_; 
v___x_3794_ = lean_st_ref_get(v_a_3772_);
v_letValue_3795_ = lean_ctor_get(v___x_3794_, 4);
lean_inc_ref(v_letValue_3795_);
lean_dec(v___x_3794_);
v___x_3796_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_letValue_3795_, v_fvarId_3770_);
lean_dec_ref(v_letValue_3795_);
if (lean_obj_tag(v___x_3796_) == 1)
{
lean_object* v___x_3798_; 
lean_del_object(v___x_3792_);
lean_dec(v_val_3784_);
lean_dec(v_fvarId_3770_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v___x_3796_);
v___x_3798_ = v___x_3788_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
else
{
lean_object* v___x_3800_; 
lean_dec(v___x_3796_);
lean_del_object(v___x_3788_);
v___x_3800_ = l_Lean_Meta_Sym_shareCommon(v_val_3784_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3835_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3803_ = v___x_3800_;
v_isShared_3804_ = v_isSharedCheck_3835_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3835_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v_share_3806_; lean_object* v_maxFVar_3807_; lean_object* v_proofInstInfo_3808_; lean_object* v_proofInstInfoFVar_3809_; lean_object* v_letValue_3810_; lean_object* v_inferType_3811_; lean_object* v_getLevel_3812_; lean_object* v_congrInfo_3813_; lean_object* v_defEqI_3814_; lean_object* v_extensions_3815_; lean_object* v_issues_3816_; lean_object* v_canon_3817_; lean_object* v_instanceOverrides_3818_; uint8_t v_debug_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3834_; 
v___x_3805_ = lean_st_ref_take(v_a_3772_);
v_share_3806_ = lean_ctor_get(v___x_3805_, 0);
v_maxFVar_3807_ = lean_ctor_get(v___x_3805_, 1);
v_proofInstInfo_3808_ = lean_ctor_get(v___x_3805_, 2);
v_proofInstInfoFVar_3809_ = lean_ctor_get(v___x_3805_, 3);
v_letValue_3810_ = lean_ctor_get(v___x_3805_, 4);
v_inferType_3811_ = lean_ctor_get(v___x_3805_, 5);
v_getLevel_3812_ = lean_ctor_get(v___x_3805_, 6);
v_congrInfo_3813_ = lean_ctor_get(v___x_3805_, 7);
v_defEqI_3814_ = lean_ctor_get(v___x_3805_, 8);
v_extensions_3815_ = lean_ctor_get(v___x_3805_, 9);
v_issues_3816_ = lean_ctor_get(v___x_3805_, 10);
v_canon_3817_ = lean_ctor_get(v___x_3805_, 11);
v_instanceOverrides_3818_ = lean_ctor_get(v___x_3805_, 12);
v_debug_3819_ = lean_ctor_get_uint8(v___x_3805_, sizeof(void*)*13);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3821_ = v___x_3805_;
v_isShared_3822_ = v_isSharedCheck_3834_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_instanceOverrides_3818_);
lean_inc(v_canon_3817_);
lean_inc(v_issues_3816_);
lean_inc(v_extensions_3815_);
lean_inc(v_defEqI_3814_);
lean_inc(v_congrInfo_3813_);
lean_inc(v_getLevel_3812_);
lean_inc(v_inferType_3811_);
lean_inc(v_letValue_3810_);
lean_inc(v_proofInstInfoFVar_3809_);
lean_inc(v_proofInstInfo_3808_);
lean_inc(v_maxFVar_3807_);
lean_inc(v_share_3806_);
lean_dec(v___x_3805_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3834_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_inc(v_a_3801_);
v___x_3823_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(v_letValue_3810_, v_fvarId_3770_, v_a_3801_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 4, v___x_3823_);
v___x_3825_ = v___x_3821_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_share_3806_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_maxFVar_3807_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_proofInstInfo_3808_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_proofInstInfoFVar_3809_);
lean_ctor_set(v_reuseFailAlloc_3833_, 4, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3833_, 5, v_inferType_3811_);
lean_ctor_set(v_reuseFailAlloc_3833_, 6, v_getLevel_3812_);
lean_ctor_set(v_reuseFailAlloc_3833_, 7, v_congrInfo_3813_);
lean_ctor_set(v_reuseFailAlloc_3833_, 8, v_defEqI_3814_);
lean_ctor_set(v_reuseFailAlloc_3833_, 9, v_extensions_3815_);
lean_ctor_set(v_reuseFailAlloc_3833_, 10, v_issues_3816_);
lean_ctor_set(v_reuseFailAlloc_3833_, 11, v_canon_3817_);
lean_ctor_set(v_reuseFailAlloc_3833_, 12, v_instanceOverrides_3818_);
lean_ctor_set_uint8(v_reuseFailAlloc_3833_, sizeof(void*)*13, v_debug_3819_);
v___x_3825_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3826_ = lean_st_ref_put(v_a_3772_, v___x_3825_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v_a_3801_);
v___x_3828_ = v___x_3792_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3801_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3828_);
v___x_3830_ = v___x_3803_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_del_object(v___x_3792_);
lean_dec(v_fvarId_3770_);
v_a_3836_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3800_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3800_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
}
else
{
lean_object* v___x_3847_; 
lean_dec(v_fvarId_3770_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v_a_3780_);
v___x_3847_ = v___x_3788_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3780_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
lean_dec(v_a_3780_);
lean_dec(v_fvarId_3770_);
v___x_3850_ = lean_box(0);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3850_);
v___x_3852_ = v___x_3782_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
else
{
lean_dec(v_fvarId_3770_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f___boxed(lean_object* v_fvarId_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Meta_Sym_getLetValueS_x3f(v_fvarId_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
lean_dec_ref(v_a_3856_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(lean_object* v_00_u03b2_3864_, lean_object* v_x_3865_, lean_object* v_x_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_x_3865_, v_x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___boxed(lean_object* v_00_u03b2_3868_, lean_object* v_x_3869_, lean_object* v_x_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(v_00_u03b2_3868_, v_x_3869_, v_x_3870_);
lean_dec(v_x_3870_);
lean_dec_ref(v_x_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1(lean_object* v_00_u03b2_3872_, lean_object* v_x_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(v_x_3873_, v_x_3874_, v_x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3877_, lean_object* v_x_3878_, size_t v_x_3879_, lean_object* v_x_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3878_, v_x_3879_, v_x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3882_, lean_object* v_x_3883_, lean_object* v_x_3884_, lean_object* v_x_3885_){
_start:
{
size_t v_x_4577__boxed_3886_; lean_object* v_res_3887_; 
v_x_4577__boxed_3886_ = lean_unbox_usize(v_x_3884_);
lean_dec(v_x_3884_);
v_res_3887_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(v_00_u03b2_3882_, v_x_3883_, v_x_4577__boxed_3886_, v_x_3885_);
lean_dec(v_x_3885_);
lean_dec_ref(v_x_3883_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(lean_object* v_00_u03b2_3888_, lean_object* v_x_3889_, size_t v_x_3890_, size_t v_x_3891_, lean_object* v_x_3892_, lean_object* v_x_3893_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3889_, v_x_3890_, v_x_3891_, v_x_3892_, v_x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3895_, lean_object* v_x_3896_, lean_object* v_x_3897_, lean_object* v_x_3898_, lean_object* v_x_3899_, lean_object* v_x_3900_){
_start:
{
size_t v_x_4588__boxed_3901_; size_t v_x_4589__boxed_3902_; lean_object* v_res_3903_; 
v_x_4588__boxed_3901_ = lean_unbox_usize(v_x_3897_);
lean_dec(v_x_3897_);
v_x_4589__boxed_3902_ = lean_unbox_usize(v_x_3898_);
lean_dec(v_x_3898_);
v_res_3903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(v_00_u03b2_3895_, v_x_3896_, v_x_4588__boxed_3901_, v_x_4589__boxed_3902_, v_x_3899_, v_x_3900_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3904_, lean_object* v_keys_3905_, lean_object* v_vals_3906_, lean_object* v_heq_3907_, lean_object* v_i_3908_, lean_object* v_k_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3905_, v_vals_3906_, v_i_3908_, v_k_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3911_, lean_object* v_keys_3912_, lean_object* v_vals_3913_, lean_object* v_heq_3914_, lean_object* v_i_3915_, lean_object* v_k_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3911_, v_keys_3912_, v_vals_3913_, v_heq_3914_, v_i_3915_, v_k_3916_);
lean_dec(v_k_3916_);
lean_dec_ref(v_vals_3913_);
lean_dec_ref(v_keys_3912_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3918_, lean_object* v_n_3919_, lean_object* v_k_3920_, lean_object* v_v_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(v_n_3919_, v_k_3920_, v_v_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3923_, size_t v_depth_3924_, lean_object* v_keys_3925_, lean_object* v_vals_3926_, lean_object* v_heq_3927_, lean_object* v_i_3928_, lean_object* v_entries_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_depth_3924_, v_keys_3925_, v_vals_3926_, v_i_3928_, v_entries_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3931_, lean_object* v_depth_3932_, lean_object* v_keys_3933_, lean_object* v_vals_3934_, lean_object* v_heq_3935_, lean_object* v_i_3936_, lean_object* v_entries_3937_){
_start:
{
size_t v_depth_boxed_3938_; lean_object* v_res_3939_; 
v_depth_boxed_3938_ = lean_unbox_usize(v_depth_3932_);
lean_dec(v_depth_3932_);
v_res_3939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(v_00_u03b2_3931_, v_depth_boxed_3938_, v_keys_3933_, v_vals_3934_, v_heq_3935_, v_i_3936_, v_entries_3937_);
lean_dec_ref(v_vals_3934_);
lean_dec_ref(v_keys_3933_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3940_, lean_object* v_x_3941_, lean_object* v_x_3942_, lean_object* v_x_3943_, lean_object* v_x_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3941_, v_x_3942_, v_x_3943_, v_x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_Meta_Sym_share(v_e_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3964_){
_start:
{
lean_object* v___x_3966_; uint8_t v_debug_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3966_ = lean_st_ref_get(v_a_3964_);
v_debug_3967_ = lean_ctor_get_uint8(v___x_3966_, sizeof(void*)*13);
lean_dec(v___x_3966_);
v___x_3968_ = lean_box(v_debug_3967_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3970_);
lean_dec(v_a_3970_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v___x_3980_; uint8_t v_debug_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3980_ = lean_st_ref_get(v_a_3974_);
v_debug_3981_ = lean_ctor_get_uint8(v___x_3980_, sizeof(void*)*13);
lean_dec(v___x_3980_);
v___x_3982_ = lean_box(v_debug_3981_);
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3992_){
_start:
{
lean_object* v_config_3994_; lean_object* v___x_3995_; 
v_config_3994_ = lean_ctor_get(v_a_3992_, 1);
lean_inc_ref(v_config_3994_);
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_config_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3996_);
lean_dec_ref(v_a_3996_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3999_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_Meta_Sym_getConfig(v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_4015_, lean_object* v_msg_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_ref_4022_; lean_object* v___x_4023_; lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4069_; 
v_ref_4022_ = lean_ctor_get(v___y_4019_, 2);
v___x_4023_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4069_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4069_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v_traceState_4029_; lean_object* v_env_4030_; lean_object* v_nextMacroScope_4031_; lean_object* v_ngen_4032_; lean_object* v_auxDeclNGen_4033_; lean_object* v_cache_4034_; lean_object* v_recordedDeps_4035_; lean_object* v_messages_4036_; lean_object* v_infoState_4037_; lean_object* v_snapshotTasks_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4068_; 
v___x_4028_ = lean_st_ref_take(v___y_4020_);
v_traceState_4029_ = lean_ctor_get(v___x_4028_, 4);
v_env_4030_ = lean_ctor_get(v___x_4028_, 0);
v_nextMacroScope_4031_ = lean_ctor_get(v___x_4028_, 1);
v_ngen_4032_ = lean_ctor_get(v___x_4028_, 2);
v_auxDeclNGen_4033_ = lean_ctor_get(v___x_4028_, 3);
v_cache_4034_ = lean_ctor_get(v___x_4028_, 5);
v_recordedDeps_4035_ = lean_ctor_get(v___x_4028_, 6);
v_messages_4036_ = lean_ctor_get(v___x_4028_, 7);
v_infoState_4037_ = lean_ctor_get(v___x_4028_, 8);
v_snapshotTasks_4038_ = lean_ctor_get(v___x_4028_, 9);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4040_ = v___x_4028_;
v_isShared_4041_ = v_isSharedCheck_4068_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_snapshotTasks_4038_);
lean_inc(v_infoState_4037_);
lean_inc(v_messages_4036_);
lean_inc(v_recordedDeps_4035_);
lean_inc(v_cache_4034_);
lean_inc(v_traceState_4029_);
lean_inc(v_auxDeclNGen_4033_);
lean_inc(v_ngen_4032_);
lean_inc(v_nextMacroScope_4031_);
lean_inc(v_env_4030_);
lean_dec(v___x_4028_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4068_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
uint64_t v_tid_4042_; lean_object* v_traces_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4067_; 
v_tid_4042_ = lean_ctor_get_uint64(v_traceState_4029_, sizeof(void*)*1);
v_traces_4043_ = lean_ctor_get(v_traceState_4029_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_traceState_4029_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4045_ = v_traceState_4029_;
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_traces_4043_);
lean_dec(v_traceState_4029_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; double v___x_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4047_ = lean_box(0);
v___x_4048_ = lean_box(0);
v___x_4049_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_4050_ = 0;
v___x_4051_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4052_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4052_, 0, v_cls_4015_);
lean_ctor_set(v___x_4052_, 1, v___x_4048_);
lean_ctor_set(v___x_4052_, 2, v___x_4051_);
lean_ctor_set_float(v___x_4052_, sizeof(void*)*3, v___x_4049_);
lean_ctor_set_float(v___x_4052_, sizeof(void*)*3 + 8, v___x_4049_);
lean_ctor_set_uint8(v___x_4052_, sizeof(void*)*3 + 16, v___x_4050_);
v___x_4053_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_4054_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4052_);
lean_ctor_set(v___x_4054_, 1, v_a_4024_);
lean_ctor_set(v___x_4054_, 2, v___x_4053_);
lean_inc(v_ref_4022_);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v_ref_4022_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = l_Lean_PersistentArray_push___redArg(v_traces_4043_, v___x_4055_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4056_);
v___x_4058_ = v___x_4045_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4056_);
lean_ctor_set_uint64(v_reuseFailAlloc_4066_, sizeof(void*)*1, v_tid_4042_);
v___x_4058_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4060_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 4, v___x_4058_);
v___x_4060_ = v___x_4040_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_env_4030_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_nextMacroScope_4031_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_ngen_4032_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_auxDeclNGen_4033_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4065_, 5, v_cache_4034_);
lean_ctor_set(v_reuseFailAlloc_4065_, 6, v_recordedDeps_4035_);
lean_ctor_set(v_reuseFailAlloc_4065_, 7, v_messages_4036_);
lean_ctor_set(v_reuseFailAlloc_4065_, 8, v_infoState_4037_);
lean_ctor_set(v_reuseFailAlloc_4065_, 9, v_snapshotTasks_4038_);
v___x_4060_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4061_ = lean_st_ref_put(v___y_4020_, v___x_4060_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4047_);
v___x_4063_ = v___x_4026_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4047_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_4070_, lean_object* v_msg_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_4070_, v_msg_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
return v_res_4077_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_4081_; uint8_t v___x_4082_; double v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4081_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4082_ = 1;
v___x_4083_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_4084_ = lean_box(0);
v___x_4085_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_4086_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___x_4084_);
lean_ctor_set(v___x_4086_, 2, v___x_4081_);
lean_ctor_set_float(v___x_4086_, sizeof(void*)*3, v___x_4083_);
lean_ctor_set_float(v___x_4086_, sizeof(void*)*3 + 8, v___x_4083_);
lean_ctor_set_uint8(v___x_4086_, sizeof(void*)*3 + 16, v___x_4082_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v___x_4098_; lean_object* v_a_4099_; lean_object* v___x_4100_; lean_object* v_share_4101_; lean_object* v_maxFVar_4102_; lean_object* v_proofInstInfo_4103_; lean_object* v_proofInstInfoFVar_4104_; lean_object* v_letValue_4105_; lean_object* v_inferType_4106_; lean_object* v_getLevel_4107_; lean_object* v_congrInfo_4108_; lean_object* v_defEqI_4109_; lean_object* v_extensions_4110_; lean_object* v_issues_4111_; lean_object* v_canon_4112_; lean_object* v_instanceOverrides_4113_; uint8_t v_debug_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4134_; 
v___x_4098_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_4087_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = lean_st_ref_take(v_a_4089_);
v_share_4101_ = lean_ctor_get(v___x_4100_, 0);
v_maxFVar_4102_ = lean_ctor_get(v___x_4100_, 1);
v_proofInstInfo_4103_ = lean_ctor_get(v___x_4100_, 2);
v_proofInstInfoFVar_4104_ = lean_ctor_get(v___x_4100_, 3);
v_letValue_4105_ = lean_ctor_get(v___x_4100_, 4);
v_inferType_4106_ = lean_ctor_get(v___x_4100_, 5);
v_getLevel_4107_ = lean_ctor_get(v___x_4100_, 6);
v_congrInfo_4108_ = lean_ctor_get(v___x_4100_, 7);
v_defEqI_4109_ = lean_ctor_get(v___x_4100_, 8);
v_extensions_4110_ = lean_ctor_get(v___x_4100_, 9);
v_issues_4111_ = lean_ctor_get(v___x_4100_, 10);
v_canon_4112_ = lean_ctor_get(v___x_4100_, 11);
v_instanceOverrides_4113_ = lean_ctor_get(v___x_4100_, 12);
v_debug_4114_ = lean_ctor_get_uint8(v___x_4100_, sizeof(void*)*13);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4116_ = v___x_4100_;
v_isShared_4117_ = v_isSharedCheck_4134_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_instanceOverrides_4113_);
lean_inc(v_canon_4112_);
lean_inc(v_issues_4111_);
lean_inc(v_extensions_4110_);
lean_inc(v_defEqI_4109_);
lean_inc(v_congrInfo_4108_);
lean_inc(v_getLevel_4107_);
lean_inc(v_inferType_4106_);
lean_inc(v_letValue_4105_);
lean_inc(v_proofInstInfoFVar_4104_);
lean_inc(v_proofInstInfo_4103_);
lean_inc(v_maxFVar_4102_);
lean_inc(v_share_4101_);
lean_dec(v___x_4100_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4134_;
goto v_resetjp_4115_;
}
v___jp_4095_:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_box(0);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
return v___x_4097_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4118_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_4119_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_4099_);
v___x_4120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v_a_4099_);
lean_ctor_set(v___x_4120_, 2, v___x_4119_);
v___x_4121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v_issues_4111_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 10, v___x_4121_);
v___x_4123_ = v___x_4116_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_share_4101_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_maxFVar_4102_);
lean_ctor_set(v_reuseFailAlloc_4133_, 2, v_proofInstInfo_4103_);
lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_proofInstInfoFVar_4104_);
lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_letValue_4105_);
lean_ctor_set(v_reuseFailAlloc_4133_, 5, v_inferType_4106_);
lean_ctor_set(v_reuseFailAlloc_4133_, 6, v_getLevel_4107_);
lean_ctor_set(v_reuseFailAlloc_4133_, 7, v_congrInfo_4108_);
lean_ctor_set(v_reuseFailAlloc_4133_, 8, v_defEqI_4109_);
lean_ctor_set(v_reuseFailAlloc_4133_, 9, v_extensions_4110_);
lean_ctor_set(v_reuseFailAlloc_4133_, 10, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4133_, 11, v_canon_4112_);
lean_ctor_set(v_reuseFailAlloc_4133_, 12, v_instanceOverrides_4113_);
lean_ctor_set_uint8(v_reuseFailAlloc_4133_, sizeof(void*)*13, v_debug_4114_);
v___x_4123_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; lean_object* v_toCold_4125_; lean_object* v_options_4126_; uint8_t v_hasTrace_4127_; 
v___x_4124_ = lean_st_ref_put(v_a_4089_, v___x_4123_);
v_toCold_4125_ = lean_ctor_get(v_a_4092_, 0);
v_options_4126_ = lean_ctor_get(v_toCold_4125_, 2);
v_hasTrace_4127_ = lean_ctor_get_uint8(v_options_4126_, sizeof(void*)*1);
if (v_hasTrace_4127_ == 0)
{
lean_dec(v_a_4099_);
goto v___jp_4095_;
}
else
{
lean_object* v_inheritedTraceOptions_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
v_inheritedTraceOptions_4128_ = lean_ctor_get(v_toCold_4125_, 11);
v___x_4129_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_4130_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_4131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4128_, v_options_4126_, v___x_4130_);
if (v___x_4131_ == 0)
{
lean_dec(v_a_4099_);
goto v___jp_4095_;
}
else
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_4129_, v_a_4099_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
return v___x_4132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Meta_Sym_reportIssue(v_msg_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_4144_, lean_object* v_msg_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_4144_, v_msg_4145_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_4154_, lean_object* v_msg_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_4154_, v_msg_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v___x_4172_; lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4183_; 
v___x_4172_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4165_);
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4183_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4183_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
uint8_t v_verbose_4177_; 
v_verbose_4177_ = lean_ctor_get_uint8(v_a_4173_, 0);
lean_dec(v_a_4173_);
if (v_verbose_4177_ == 0)
{
lean_object* v___x_4178_; lean_object* v___x_4180_; 
lean_dec_ref(v_msg_4164_);
v___x_4178_ = lean_box(0);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4178_);
v___x_4180_ = v___x_4175_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
else
{
lean_object* v___x_4182_; 
lean_del_object(v___x_4175_);
v___x_4182_ = l_Lean_Meta_Sym_reportIssue(v_msg_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
return v___x_4182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
return v_res_4192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_4209_ = l_String_toRawSubstring_x27(v___x_4208_);
return v___x_4209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4247_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4248_ = l_String_toRawSubstring_x27(v___x_4247_);
return v___x_4248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_4261_ = l_String_toRawSubstring_x27(v___x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v_msg_4288_; lean_object* v_quotContext_4289_; lean_object* v_currMacroScope_4290_; lean_object* v_ref_4291_; lean_object* v___y_4292_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
lean_inc(v_s_4284_);
v___x_4307_ = l_Lean_Syntax_getKind(v_s_4284_);
v___x_4308_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4309_ = lean_name_eq(v___x_4307_, v___x_4308_);
lean_dec(v___x_4307_);
if (v___x_4309_ == 0)
{
lean_object* v_quotContext_4310_; lean_object* v_currMacroScope_4311_; lean_object* v_ref_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v_quotContext_4310_ = lean_ctor_get(v_a_4285_, 1);
v_currMacroScope_4311_ = lean_ctor_get(v_a_4285_, 2);
v_ref_4312_ = lean_ctor_get(v_a_4285_, 5);
v___x_4313_ = l_Lean_SourceInfo_fromRef(v_ref_4312_, v___x_4309_);
v___x_4314_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4316_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4313_, 8);
v___x_4317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4313_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v___x_4318_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4319_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4320_ = lean_box(0);
lean_inc_n(v_currMacroScope_4311_, 3);
lean_inc_n(v_quotContext_4310_, 3);
v___x_4321_ = l_Lean_addMacroScope(v_quotContext_4310_, v___x_4320_, v_currMacroScope_4311_);
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4313_);
lean_ctor_set(v___x_4323_, 1, v___x_4319_);
lean_ctor_set(v___x_4323_, 2, v___x_4321_);
lean_ctor_set(v___x_4323_, 3, v___x_4322_);
v___x_4324_ = l_Lean_Syntax_node1(v___x_4313_, v___x_4318_, v___x_4323_);
v___x_4325_ = l_Lean_Syntax_node2(v___x_4313_, v___x_4315_, v___x_4317_, v___x_4324_);
v___x_4326_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4313_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4329_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4330_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4331_ = l_Lean_addMacroScope(v_quotContext_4310_, v___x_4330_, v_currMacroScope_4311_);
v___x_4332_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4313_);
lean_ctor_set(v___x_4333_, 1, v___x_4329_);
lean_ctor_set(v___x_4333_, 2, v___x_4331_);
lean_ctor_set(v___x_4333_, 3, v___x_4332_);
v___x_4334_ = l_Lean_Syntax_node1(v___x_4313_, v___x_4328_, v___x_4333_);
v___x_4335_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4313_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_node5(v___x_4313_, v___x_4314_, v___x_4325_, v_s_4284_, v___x_4327_, v___x_4334_, v___x_4336_);
v_msg_4288_ = v___x_4337_;
v_quotContext_4289_ = v_quotContext_4310_;
v_currMacroScope_4290_ = v_currMacroScope_4311_;
v_ref_4291_ = v_ref_4312_;
v___y_4292_ = v_a_4286_;
goto v___jp_4287_;
}
else
{
lean_object* v_quotContext_4338_; lean_object* v_currMacroScope_4339_; lean_object* v_ref_4340_; uint8_t v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_quotContext_4338_ = lean_ctor_get(v_a_4285_, 1);
v_currMacroScope_4339_ = lean_ctor_get(v_a_4285_, 2);
v_ref_4340_ = lean_ctor_get(v_a_4285_, 5);
v___x_4341_ = 0;
v___x_4342_ = l_Lean_SourceInfo_fromRef(v_ref_4340_, v___x_4341_);
v___x_4343_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4344_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4342_);
v___x_4345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4342_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_node2(v___x_4342_, v___x_4343_, v___x_4345_, v_s_4284_);
lean_inc(v_currMacroScope_4339_);
lean_inc(v_quotContext_4338_);
v_msg_4288_ = v___x_4346_;
v_quotContext_4289_ = v_quotContext_4338_;
v_currMacroScope_4290_ = v_currMacroScope_4339_;
v_ref_4291_ = v_ref_4340_;
v___y_4292_ = v_a_4286_;
goto v___jp_4287_;
}
v___jp_4287_:
{
uint8_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4293_ = 0;
v___x_4294_ = l_Lean_SourceInfo_fromRef(v_ref_4291_, v___x_4293_);
v___x_4295_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4296_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4297_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_4298_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_4299_ = l_Lean_addMacroScope(v_quotContext_4289_, v___x_4298_, v_currMacroScope_4290_);
v___x_4300_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_4294_, 3);
v___x_4301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4294_);
lean_ctor_set(v___x_4301_, 1, v___x_4297_);
lean_ctor_set(v___x_4301_, 2, v___x_4299_);
lean_ctor_set(v___x_4301_, 3, v___x_4300_);
v___x_4302_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4303_ = l_Lean_Syntax_node1(v___x_4294_, v___x_4302_, v_msg_4288_);
v___x_4304_ = l_Lean_Syntax_node2(v___x_4294_, v___x_4296_, v___x_4301_, v___x_4303_);
v___x_4305_ = l_Lean_Syntax_node1(v___x_4294_, v___x_4295_, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v___y_4292_);
return v___x_4306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_4347_, v_a_4348_, v_a_4349_);
lean_dec_ref(v_a_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4394_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_4391_);
v___x_4395_ = l_Lean_Syntax_isOfKind(v_x_4391_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_dec(v_x_4391_);
v___x_4396_ = lean_box(1);
v___x_4397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v_a_4393_);
return v___x_4397_;
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v_a_4401_; lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v___x_4398_ = lean_unsigned_to_nat(1u);
v___x_4399_ = l_Lean_Syntax_getArg(v_x_4391_, v___x_4398_);
lean_dec(v_x_4391_);
v___x_4400_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_4399_, v_a_4392_, v_a_4393_);
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_a_4402_ = lean_ctor_get(v___x_4400_, 1);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4400_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4401_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4410_, v_a_4411_, v_a_4412_);
lean_dec_ref(v_a_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4442_; 
v___x_4422_ = l_Lean_KVMap_instValueBool;
v___x_4423_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4415_);
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4442_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4442_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
uint8_t v_verbose_4428_; 
v_verbose_4428_ = lean_ctor_get_uint8(v_a_4424_, 0);
lean_dec(v_a_4424_);
if (v_verbose_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_dec_ref(v_msg_4414_);
v___x_4429_ = lean_box(0);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v___x_4429_);
v___x_4431_ = v___x_4426_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
else
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v___x_4433_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4419_);
v___x_4434_ = l_Lean_Meta_Sym_sym_debug;
v___x_4435_ = l_Lean_Option_get___redArg(v___x_4422_, v___x_4433_, v___x_4434_);
lean_dec_ref(v___x_4433_);
v___x_4436_ = lean_unbox(v___x_4435_);
lean_dec(v___x_4435_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
lean_dec_ref(v_msg_4414_);
v___x_4437_ = lean_box(0);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v___x_4437_);
v___x_4439_ = v___x_4426_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
else
{
lean_object* v___x_4441_; 
lean_del_object(v___x_4426_);
v___x_4441_ = l_Lean_Meta_Sym_reportIssue(v_msg_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
return v___x_4441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
return v_res_4451_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4454_ = l_String_toRawSubstring_x27(v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_msg_4474_; lean_object* v_quotContext_4475_; lean_object* v_currMacroScope_4476_; lean_object* v_ref_4477_; lean_object* v___y_4478_; lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
lean_inc(v_s_4470_);
v___x_4493_ = l_Lean_Syntax_getKind(v_s_4470_);
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4495_ = lean_name_eq(v___x_4493_, v___x_4494_);
lean_dec(v___x_4493_);
if (v___x_4495_ == 0)
{
lean_object* v_quotContext_4496_; lean_object* v_currMacroScope_4497_; lean_object* v_ref_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v_quotContext_4496_ = lean_ctor_get(v_a_4471_, 1);
v_currMacroScope_4497_ = lean_ctor_get(v_a_4471_, 2);
v_ref_4498_ = lean_ctor_get(v_a_4471_, 5);
v___x_4499_ = l_Lean_SourceInfo_fromRef(v_ref_4498_, v___x_4495_);
v___x_4500_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4501_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4502_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4499_, 8);
v___x_4503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4499_);
lean_ctor_set(v___x_4503_, 1, v___x_4502_);
v___x_4504_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4505_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4506_ = lean_box(0);
lean_inc_n(v_currMacroScope_4497_, 3);
lean_inc_n(v_quotContext_4496_, 3);
v___x_4507_ = l_Lean_addMacroScope(v_quotContext_4496_, v___x_4506_, v_currMacroScope_4497_);
v___x_4508_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4509_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4499_);
lean_ctor_set(v___x_4509_, 1, v___x_4505_);
lean_ctor_set(v___x_4509_, 2, v___x_4507_);
lean_ctor_set(v___x_4509_, 3, v___x_4508_);
v___x_4510_ = l_Lean_Syntax_node1(v___x_4499_, v___x_4504_, v___x_4509_);
v___x_4511_ = l_Lean_Syntax_node2(v___x_4499_, v___x_4501_, v___x_4503_, v___x_4510_);
v___x_4512_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4499_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
v___x_4514_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4515_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4516_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4517_ = l_Lean_addMacroScope(v_quotContext_4496_, v___x_4516_, v_currMacroScope_4497_);
v___x_4518_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4499_);
lean_ctor_set(v___x_4519_, 1, v___x_4515_);
lean_ctor_set(v___x_4519_, 2, v___x_4517_);
lean_ctor_set(v___x_4519_, 3, v___x_4518_);
v___x_4520_ = l_Lean_Syntax_node1(v___x_4499_, v___x_4514_, v___x_4519_);
v___x_4521_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4499_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
v___x_4523_ = l_Lean_Syntax_node5(v___x_4499_, v___x_4500_, v___x_4511_, v_s_4470_, v___x_4513_, v___x_4520_, v___x_4522_);
v_msg_4474_ = v___x_4523_;
v_quotContext_4475_ = v_quotContext_4496_;
v_currMacroScope_4476_ = v_currMacroScope_4497_;
v_ref_4477_ = v_ref_4498_;
v___y_4478_ = v_a_4472_;
goto v___jp_4473_;
}
else
{
lean_object* v_quotContext_4524_; lean_object* v_currMacroScope_4525_; lean_object* v_ref_4526_; uint8_t v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v_quotContext_4524_ = lean_ctor_get(v_a_4471_, 1);
v_currMacroScope_4525_ = lean_ctor_get(v_a_4471_, 2);
v_ref_4526_ = lean_ctor_get(v_a_4471_, 5);
v___x_4527_ = 0;
v___x_4528_ = l_Lean_SourceInfo_fromRef(v_ref_4526_, v___x_4527_);
v___x_4529_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4530_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4528_);
v___x_4531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4528_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
v___x_4532_ = l_Lean_Syntax_node2(v___x_4528_, v___x_4529_, v___x_4531_, v_s_4470_);
lean_inc(v_currMacroScope_4525_);
lean_inc(v_quotContext_4524_);
v_msg_4474_ = v___x_4532_;
v_quotContext_4475_ = v_quotContext_4524_;
v_currMacroScope_4476_ = v_currMacroScope_4525_;
v_ref_4477_ = v_ref_4526_;
v___y_4478_ = v_a_4472_;
goto v___jp_4473_;
}
v___jp_4473_:
{
uint8_t v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4479_ = 0;
v___x_4480_ = l_Lean_SourceInfo_fromRef(v_ref_4477_, v___x_4479_);
v___x_4481_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4483_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4484_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4485_ = l_Lean_addMacroScope(v_quotContext_4475_, v___x_4484_, v_currMacroScope_4476_);
v___x_4486_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4480_, 3);
v___x_4487_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4480_);
lean_ctor_set(v___x_4487_, 1, v___x_4483_);
lean_ctor_set(v___x_4487_, 2, v___x_4485_);
lean_ctor_set(v___x_4487_, 3, v___x_4486_);
v___x_4488_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4489_ = l_Lean_Syntax_node1(v___x_4480_, v___x_4488_, v_msg_4474_);
v___x_4490_ = l_Lean_Syntax_node2(v___x_4480_, v___x_4482_, v___x_4487_, v___x_4489_);
v___x_4491_ = l_Lean_Syntax_node1(v___x_4480_, v___x_4481_, v___x_4490_);
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v___y_4478_);
return v___x_4492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4533_, v_a_4534_, v_a_4535_);
lean_dec_ref(v_a_4534_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4558_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4555_);
v___x_4559_ = l_Lean_Syntax_isOfKind(v_x_4555_, v___x_4558_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
lean_dec(v_x_4555_);
v___x_4560_ = lean_box(1);
v___x_4561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v_a_4557_);
return v___x_4561_;
}
else
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v_a_4565_; lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
v___x_4562_ = lean_unsigned_to_nat(1u);
v___x_4563_ = l_Lean_Syntax_getArg(v_x_4555_, v___x_4562_);
lean_dec(v_x_4555_);
v___x_4564_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4563_, v_a_4556_, v_a_4557_);
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
v_a_4566_ = lean_ctor_get(v___x_4564_, 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4564_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_inc(v_a_4565_);
lean_dec(v___x_4564_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4565_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4574_, v_a_4575_, v_a_4576_);
lean_dec_ref(v_a_4575_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4578_){
_start:
{
lean_object* v___x_4580_; lean_object* v_issues_4581_; lean_object* v___x_4582_; 
v___x_4580_ = lean_st_ref_get(v_a_4578_);
v_issues_4581_ = lean_ctor_get(v___x_4580_, 10);
lean_inc(v_issues_4581_);
lean_dec(v___x_4580_);
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v_issues_4581_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4583_);
lean_dec(v_a_4583_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4587_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Lean_Meta_Sym_getIssues(v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4602_, lean_object* v_issues_4603_, lean_object* v_a_x3f_4604_){
_start:
{
lean_object* v___x_4606_; lean_object* v_share_4607_; lean_object* v_maxFVar_4608_; lean_object* v_proofInstInfo_4609_; lean_object* v_proofInstInfoFVar_4610_; lean_object* v_letValue_4611_; lean_object* v_inferType_4612_; lean_object* v_getLevel_4613_; lean_object* v_congrInfo_4614_; lean_object* v_defEqI_4615_; lean_object* v_extensions_4616_; lean_object* v_issues_4617_; lean_object* v_canon_4618_; lean_object* v_instanceOverrides_4619_; uint8_t v_debug_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4631_; 
v___x_4606_ = lean_st_ref_take(v_a_4602_);
v_share_4607_ = lean_ctor_get(v___x_4606_, 0);
v_maxFVar_4608_ = lean_ctor_get(v___x_4606_, 1);
v_proofInstInfo_4609_ = lean_ctor_get(v___x_4606_, 2);
v_proofInstInfoFVar_4610_ = lean_ctor_get(v___x_4606_, 3);
v_letValue_4611_ = lean_ctor_get(v___x_4606_, 4);
v_inferType_4612_ = lean_ctor_get(v___x_4606_, 5);
v_getLevel_4613_ = lean_ctor_get(v___x_4606_, 6);
v_congrInfo_4614_ = lean_ctor_get(v___x_4606_, 7);
v_defEqI_4615_ = lean_ctor_get(v___x_4606_, 8);
v_extensions_4616_ = lean_ctor_get(v___x_4606_, 9);
v_issues_4617_ = lean_ctor_get(v___x_4606_, 10);
v_canon_4618_ = lean_ctor_get(v___x_4606_, 11);
v_instanceOverrides_4619_ = lean_ctor_get(v___x_4606_, 12);
v_debug_4620_ = lean_ctor_get_uint8(v___x_4606_, sizeof(void*)*13);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4622_ = v___x_4606_;
v_isShared_4623_ = v_isSharedCheck_4631_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_instanceOverrides_4619_);
lean_inc(v_canon_4618_);
lean_inc(v_issues_4617_);
lean_inc(v_extensions_4616_);
lean_inc(v_defEqI_4615_);
lean_inc(v_congrInfo_4614_);
lean_inc(v_getLevel_4613_);
lean_inc(v_inferType_4612_);
lean_inc(v_letValue_4611_);
lean_inc(v_proofInstInfoFVar_4610_);
lean_inc(v_proofInstInfo_4609_);
lean_inc(v_maxFVar_4608_);
lean_inc(v_share_4607_);
lean_dec(v___x_4606_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4631_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4624_ = lean_box(0);
v___x_4625_ = l_List_appendTR___redArg(v_issues_4617_, v_issues_4603_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 10, v___x_4625_);
v___x_4627_ = v___x_4622_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_share_4607_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_maxFVar_4608_);
lean_ctor_set(v_reuseFailAlloc_4630_, 2, v_proofInstInfo_4609_);
lean_ctor_set(v_reuseFailAlloc_4630_, 3, v_proofInstInfoFVar_4610_);
lean_ctor_set(v_reuseFailAlloc_4630_, 4, v_letValue_4611_);
lean_ctor_set(v_reuseFailAlloc_4630_, 5, v_inferType_4612_);
lean_ctor_set(v_reuseFailAlloc_4630_, 6, v_getLevel_4613_);
lean_ctor_set(v_reuseFailAlloc_4630_, 7, v_congrInfo_4614_);
lean_ctor_set(v_reuseFailAlloc_4630_, 8, v_defEqI_4615_);
lean_ctor_set(v_reuseFailAlloc_4630_, 9, v_extensions_4616_);
lean_ctor_set(v_reuseFailAlloc_4630_, 10, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4630_, 11, v_canon_4618_);
lean_ctor_set(v_reuseFailAlloc_4630_, 12, v_instanceOverrides_4619_);
lean_ctor_set_uint8(v_reuseFailAlloc_4630_, sizeof(void*)*13, v_debug_4620_);
v___x_4627_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = lean_st_ref_put(v_a_4602_, v___x_4627_);
v___x_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4624_);
return v___x_4629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4632_, lean_object* v_issues_4633_, lean_object* v_a_x3f_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4632_, v_issues_4633_, v_a_x3f_4634_);
lean_dec(v_a_x3f_4634_);
lean_dec(v_a_4632_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v___x_4645_; lean_object* v_issues_4646_; lean_object* v___x_4647_; lean_object* v_share_4648_; lean_object* v_maxFVar_4649_; lean_object* v_proofInstInfo_4650_; lean_object* v_proofInstInfoFVar_4651_; lean_object* v_letValue_4652_; lean_object* v_inferType_4653_; lean_object* v_getLevel_4654_; lean_object* v_congrInfo_4655_; lean_object* v_defEqI_4656_; lean_object* v_extensions_4657_; lean_object* v_canon_4658_; lean_object* v_instanceOverrides_4659_; uint8_t v_debug_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4698_; 
v___x_4645_ = lean_st_ref_get(v_a_4639_);
v_issues_4646_ = lean_ctor_get(v___x_4645_, 10);
lean_inc(v_issues_4646_);
lean_dec(v___x_4645_);
v___x_4647_ = lean_st_ref_take(v_a_4639_);
v_share_4648_ = lean_ctor_get(v___x_4647_, 0);
v_maxFVar_4649_ = lean_ctor_get(v___x_4647_, 1);
v_proofInstInfo_4650_ = lean_ctor_get(v___x_4647_, 2);
v_proofInstInfoFVar_4651_ = lean_ctor_get(v___x_4647_, 3);
v_letValue_4652_ = lean_ctor_get(v___x_4647_, 4);
v_inferType_4653_ = lean_ctor_get(v___x_4647_, 5);
v_getLevel_4654_ = lean_ctor_get(v___x_4647_, 6);
v_congrInfo_4655_ = lean_ctor_get(v___x_4647_, 7);
v_defEqI_4656_ = lean_ctor_get(v___x_4647_, 8);
v_extensions_4657_ = lean_ctor_get(v___x_4647_, 9);
v_canon_4658_ = lean_ctor_get(v___x_4647_, 11);
v_instanceOverrides_4659_ = lean_ctor_get(v___x_4647_, 12);
v_debug_4660_ = lean_ctor_get_uint8(v___x_4647_, sizeof(void*)*13);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; 
v_unused_4699_ = lean_ctor_get(v___x_4647_, 10);
lean_dec(v_unused_4699_);
v___x_4662_ = v___x_4647_;
v_isShared_4663_ = v_isSharedCheck_4698_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_instanceOverrides_4659_);
lean_inc(v_canon_4658_);
lean_inc(v_extensions_4657_);
lean_inc(v_defEqI_4656_);
lean_inc(v_congrInfo_4655_);
lean_inc(v_getLevel_4654_);
lean_inc(v_inferType_4653_);
lean_inc(v_letValue_4652_);
lean_inc(v_proofInstInfoFVar_4651_);
lean_inc(v_proofInstInfo_4650_);
lean_inc(v_maxFVar_4649_);
lean_inc(v_share_4648_);
lean_dec(v___x_4647_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4698_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4664_ = lean_box(0);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 10, v___x_4664_);
v___x_4666_ = v___x_4662_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_share_4648_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_maxFVar_4649_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_proofInstInfo_4650_);
lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_proofInstInfoFVar_4651_);
lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_letValue_4652_);
lean_ctor_set(v_reuseFailAlloc_4697_, 5, v_inferType_4653_);
lean_ctor_set(v_reuseFailAlloc_4697_, 6, v_getLevel_4654_);
lean_ctor_set(v_reuseFailAlloc_4697_, 7, v_congrInfo_4655_);
lean_ctor_set(v_reuseFailAlloc_4697_, 8, v_defEqI_4656_);
lean_ctor_set(v_reuseFailAlloc_4697_, 9, v_extensions_4657_);
lean_ctor_set(v_reuseFailAlloc_4697_, 10, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4697_, 11, v_canon_4658_);
lean_ctor_set(v_reuseFailAlloc_4697_, 12, v_instanceOverrides_4659_);
lean_ctor_set_uint8(v_reuseFailAlloc_4697_, sizeof(void*)*13, v_debug_4660_);
v___x_4666_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4667_; lean_object* v_r_4668_; 
v___x_4667_ = lean_st_ref_put(v_a_4639_, v___x_4666_);
lean_inc(v_a_4643_);
lean_inc_ref(v_a_4642_);
lean_inc(v_a_4641_);
lean_inc_ref(v_a_4640_);
lean_inc(v_a_4639_);
lean_inc_ref(v_a_4638_);
v_r_4668_ = lean_apply_7(v_x_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, lean_box(0));
if (lean_obj_tag(v_r_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4685_; 
v_a_4669_ = lean_ctor_get(v_r_4668_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v_r_4668_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4671_ = v_r_4668_;
v_isShared_4672_ = v_isSharedCheck_4685_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v_r_4668_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4685_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
lean_inc(v_a_4669_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 1);
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
lean_object* v___x_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
v___x_4675_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4639_, v_issues_4646_, v___x_4674_);
lean_dec_ref(v___x_4674_);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4682_ == 0)
{
lean_object* v_unused_4683_; 
v_unused_4683_ = lean_ctor_get(v___x_4675_, 0);
lean_dec(v_unused_4683_);
v___x_4677_ = v___x_4675_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_dec(v___x_4675_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 0, v_a_4669_);
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4669_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
v_a_4686_ = lean_ctor_get(v_r_4668_, 0);
lean_inc(v_a_4686_);
lean_dec_ref_known(v_r_4668_, 1);
v___x_4687_ = lean_box(0);
v___x_4688_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4639_, v_issues_4646_, v___x_4687_);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4695_ == 0)
{
lean_object* v_unused_4696_; 
v_unused_4696_ = lean_ctor_get(v___x_4688_, 0);
lean_dec(v_unused_4696_);
v___x_4690_ = v___x_4688_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_dec(v___x_4688_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
lean_ctor_set_tag(v___x_4690_, 1);
lean_ctor_set(v___x_4690_, 0, v_a_4686_);
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4686_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
lean_dec(v_a_4706_);
lean_dec_ref(v_a_4705_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4709_, lean_object* v_x_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4719_, lean_object* v_x_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4719_, v_x_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4729_, lean_object* v_vals_4730_, lean_object* v_i_4731_, lean_object* v_k_4732_){
_start:
{
lean_object* v___x_4737_; uint8_t v___x_4738_; 
v___x_4737_ = lean_array_get_size(v_keys_4729_);
v___x_4738_ = lean_nat_dec_lt(v_i_4731_, v___x_4737_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; 
lean_dec(v_i_4731_);
v___x_4739_ = lean_box(0);
return v___x_4739_;
}
else
{
lean_object* v_fst_4740_; lean_object* v_snd_4741_; lean_object* v_k_x27_4742_; lean_object* v_fst_4743_; lean_object* v_snd_4744_; size_t v___x_4745_; size_t v___x_4746_; uint8_t v___x_4747_; 
v_fst_4740_ = lean_ctor_get(v_k_4732_, 0);
v_snd_4741_ = lean_ctor_get(v_k_4732_, 1);
v_k_x27_4742_ = lean_array_fget_borrowed(v_keys_4729_, v_i_4731_);
v_fst_4743_ = lean_ctor_get(v_k_x27_4742_, 0);
v_snd_4744_ = lean_ctor_get(v_k_x27_4742_, 1);
v___x_4745_ = lean_ptr_addr(v_fst_4740_);
v___x_4746_ = lean_ptr_addr(v_fst_4743_);
v___x_4747_ = lean_usize_dec_eq(v___x_4745_, v___x_4746_);
if (v___x_4747_ == 0)
{
goto v___jp_4733_;
}
else
{
size_t v___x_4748_; size_t v___x_4749_; uint8_t v___x_4750_; 
v___x_4748_ = lean_ptr_addr(v_snd_4741_);
v___x_4749_ = lean_ptr_addr(v_snd_4744_);
v___x_4750_ = lean_usize_dec_eq(v___x_4748_, v___x_4749_);
if (v___x_4750_ == 0)
{
goto v___jp_4733_;
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = lean_array_fget_borrowed(v_vals_4730_, v_i_4731_);
lean_dec(v_i_4731_);
lean_inc(v___x_4751_);
v___x_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
return v___x_4752_;
}
}
}
v___jp_4733_:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = lean_unsigned_to_nat(1u);
v___x_4735_ = lean_nat_add(v_i_4731_, v___x_4734_);
lean_dec(v_i_4731_);
v_i_4731_ = v___x_4735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4753_, lean_object* v_vals_4754_, lean_object* v_i_4755_, lean_object* v_k_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4753_, v_vals_4754_, v_i_4755_, v_k_4756_);
lean_dec_ref(v_k_4756_);
lean_dec_ref(v_vals_4754_);
lean_dec_ref(v_keys_4753_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4758_, size_t v_x_4759_, lean_object* v_x_4760_){
_start:
{
if (lean_obj_tag(v_x_4758_) == 0)
{
lean_object* v_es_4761_; lean_object* v___x_4762_; size_t v___x_4763_; size_t v___x_4764_; lean_object* v_j_4765_; lean_object* v___x_4766_; 
v_es_4761_ = lean_ctor_get(v_x_4758_, 0);
v___x_4762_ = lean_box(2);
v___x_4763_ = ((size_t)31ULL);
v___x_4764_ = lean_usize_land(v_x_4759_, v___x_4763_);
v_j_4765_ = lean_usize_to_nat(v___x_4764_);
v___x_4766_ = lean_array_get_borrowed(v___x_4762_, v_es_4761_, v_j_4765_);
lean_dec(v_j_4765_);
switch(lean_obj_tag(v___x_4766_))
{
case 0:
{
lean_object* v_key_4767_; lean_object* v_val_4768_; lean_object* v_fst_4769_; lean_object* v_snd_4770_; lean_object* v_fst_4771_; lean_object* v_snd_4772_; size_t v___x_4773_; size_t v___x_4774_; uint8_t v___x_4775_; 
v_key_4767_ = lean_ctor_get(v___x_4766_, 0);
v_val_4768_ = lean_ctor_get(v___x_4766_, 1);
v_fst_4769_ = lean_ctor_get(v_x_4760_, 0);
v_snd_4770_ = lean_ctor_get(v_x_4760_, 1);
v_fst_4771_ = lean_ctor_get(v_key_4767_, 0);
v_snd_4772_ = lean_ctor_get(v_key_4767_, 1);
v___x_4773_ = lean_ptr_addr(v_fst_4769_);
v___x_4774_ = lean_ptr_addr(v_fst_4771_);
v___x_4775_ = lean_usize_dec_eq(v___x_4773_, v___x_4774_);
if (v___x_4775_ == 0)
{
lean_object* v___x_4776_; 
v___x_4776_ = lean_box(0);
return v___x_4776_;
}
else
{
size_t v___x_4777_; size_t v___x_4778_; uint8_t v___x_4779_; 
v___x_4777_ = lean_ptr_addr(v_snd_4770_);
v___x_4778_ = lean_ptr_addr(v_snd_4772_);
v___x_4779_ = lean_usize_dec_eq(v___x_4777_, v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_box(0);
return v___x_4780_;
}
else
{
lean_object* v___x_4781_; 
lean_inc(v_val_4768_);
v___x_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4781_, 0, v_val_4768_);
return v___x_4781_;
}
}
}
case 1:
{
lean_object* v_node_4782_; size_t v___x_4783_; size_t v___x_4784_; 
v_node_4782_ = lean_ctor_get(v___x_4766_, 0);
v___x_4783_ = ((size_t)5ULL);
v___x_4784_ = lean_usize_shift_right(v_x_4759_, v___x_4783_);
v_x_4758_ = v_node_4782_;
v_x_4759_ = v___x_4784_;
goto _start;
}
default: 
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_box(0);
return v___x_4786_;
}
}
}
else
{
lean_object* v_ks_4787_; lean_object* v_vs_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v_ks_4787_ = lean_ctor_get(v_x_4758_, 0);
v_vs_4788_ = lean_ctor_get(v_x_4758_, 1);
v___x_4789_ = lean_unsigned_to_nat(0u);
v___x_4790_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4787_, v_vs_4788_, v___x_4789_, v_x_4760_);
return v___x_4790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4791_, lean_object* v_x_4792_, lean_object* v_x_4793_){
_start:
{
size_t v_x_2905__boxed_4794_; lean_object* v_res_4795_; 
v_x_2905__boxed_4794_ = lean_unbox_usize(v_x_4792_);
lean_dec(v_x_4792_);
v_res_4795_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4791_, v_x_2905__boxed_4794_, v_x_4793_);
lean_dec_ref(v_x_4793_);
lean_dec_ref(v_x_4791_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4796_, lean_object* v_x_4797_){
_start:
{
lean_object* v_fst_4798_; lean_object* v_snd_4799_; size_t v___x_4800_; size_t v___x_4801_; size_t v___x_4802_; uint64_t v___x_4803_; size_t v___x_4804_; size_t v___x_4805_; uint64_t v___x_4806_; uint64_t v___x_4807_; size_t v___x_4808_; lean_object* v___x_4809_; 
v_fst_4798_ = lean_ctor_get(v_x_4797_, 0);
v_snd_4799_ = lean_ctor_get(v_x_4797_, 1);
v___x_4800_ = lean_ptr_addr(v_fst_4798_);
v___x_4801_ = ((size_t)3ULL);
v___x_4802_ = lean_usize_shift_right(v___x_4800_, v___x_4801_);
v___x_4803_ = lean_usize_to_uint64(v___x_4802_);
v___x_4804_ = lean_ptr_addr(v_snd_4799_);
v___x_4805_ = lean_usize_shift_right(v___x_4804_, v___x_4801_);
v___x_4806_ = lean_usize_to_uint64(v___x_4805_);
v___x_4807_ = lean_uint64_mix_hash(v___x_4803_, v___x_4806_);
v___x_4808_ = lean_uint64_to_usize(v___x_4807_);
v___x_4809_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4796_, v___x_4808_, v_x_4797_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4810_, lean_object* v_x_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4810_, v_x_4811_);
lean_dec_ref(v_x_4811_);
lean_dec_ref(v_x_4810_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4813_, lean_object* v_x_4814_, lean_object* v_x_4815_, lean_object* v_x_4816_){
_start:
{
lean_object* v_ks_4817_; lean_object* v_vs_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4854_; 
v_ks_4817_ = lean_ctor_get(v_x_4813_, 0);
v_vs_4818_ = lean_ctor_get(v_x_4813_, 1);
v_isSharedCheck_4854_ = !lean_is_exclusive(v_x_4813_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4820_ = v_x_4813_;
v_isShared_4821_ = v_isSharedCheck_4854_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_vs_4818_);
lean_inc(v_ks_4817_);
lean_dec(v_x_4813_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4854_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4829_ = lean_array_get_size(v_ks_4817_);
v___x_4830_ = lean_nat_dec_lt(v_x_4814_, v___x_4829_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
lean_del_object(v___x_4820_);
lean_dec(v_x_4814_);
v___x_4831_ = lean_array_push(v_ks_4817_, v_x_4815_);
v___x_4832_ = lean_array_push(v_vs_4818_, v_x_4816_);
v___x_4833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4831_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
return v___x_4833_;
}
else
{
lean_object* v_fst_4834_; lean_object* v_snd_4835_; lean_object* v_k_x27_4836_; lean_object* v_fst_4837_; lean_object* v_snd_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4853_; 
v_fst_4834_ = lean_ctor_get(v_x_4815_, 0);
v_snd_4835_ = lean_ctor_get(v_x_4815_, 1);
v_k_x27_4836_ = lean_array_fget(v_ks_4817_, v_x_4814_);
v_fst_4837_ = lean_ctor_get(v_k_x27_4836_, 0);
v_snd_4838_ = lean_ctor_get(v_k_x27_4836_, 1);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_k_x27_4836_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4840_ = v_k_x27_4836_;
v_isShared_4841_ = v_isSharedCheck_4853_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_snd_4838_);
lean_inc(v_fst_4837_);
lean_dec(v_k_x27_4836_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4853_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
size_t v___x_4842_; size_t v___x_4843_; uint8_t v___x_4844_; 
v___x_4842_ = lean_ptr_addr(v_fst_4834_);
v___x_4843_ = lean_ptr_addr(v_fst_4837_);
lean_dec(v_fst_4837_);
v___x_4844_ = lean_usize_dec_eq(v___x_4842_, v___x_4843_);
if (v___x_4844_ == 0)
{
lean_del_object(v___x_4840_);
lean_dec(v_snd_4838_);
goto v___jp_4822_;
}
else
{
size_t v___x_4845_; size_t v___x_4846_; uint8_t v___x_4847_; 
v___x_4845_ = lean_ptr_addr(v_snd_4835_);
v___x_4846_ = lean_ptr_addr(v_snd_4838_);
lean_dec(v_snd_4838_);
v___x_4847_ = lean_usize_dec_eq(v___x_4845_, v___x_4846_);
if (v___x_4847_ == 0)
{
lean_del_object(v___x_4840_);
goto v___jp_4822_;
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4851_; 
lean_del_object(v___x_4820_);
v___x_4848_ = lean_array_fset(v_ks_4817_, v_x_4814_, v_x_4815_);
v___x_4849_ = lean_array_fset(v_vs_4818_, v_x_4814_, v_x_4816_);
lean_dec(v_x_4814_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set_tag(v___x_4840_, 1);
lean_ctor_set(v___x_4840_, 1, v___x_4849_);
lean_ctor_set(v___x_4840_, 0, v___x_4848_);
v___x_4851_ = v___x_4840_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4848_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
v___jp_4822_:
{
lean_object* v___x_4824_; 
if (v_isShared_4821_ == 0)
{
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_ks_4817_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v_vs_4818_);
v___x_4824_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = lean_unsigned_to_nat(1u);
v___x_4826_ = lean_nat_add(v_x_4814_, v___x_4825_);
lean_dec(v_x_4814_);
v_x_4813_ = v___x_4824_;
v_x_4814_ = v___x_4826_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4855_, lean_object* v_k_4856_, lean_object* v_v_4857_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = lean_unsigned_to_nat(0u);
v___x_4859_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4855_, v___x_4858_, v_k_4856_, v_v_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4860_, size_t v_x_4861_, size_t v_x_4862_, lean_object* v_x_4863_, lean_object* v_x_4864_){
_start:
{
if (lean_obj_tag(v_x_4860_) == 0)
{
lean_object* v_es_4865_; size_t v___x_4866_; size_t v___x_4867_; lean_object* v_j_4868_; lean_object* v___x_4869_; uint8_t v___x_4870_; 
v_es_4865_ = lean_ctor_get(v_x_4860_, 0);
v___x_4866_ = ((size_t)31ULL);
v___x_4867_ = lean_usize_land(v_x_4861_, v___x_4866_);
v_j_4868_ = lean_usize_to_nat(v___x_4867_);
v___x_4869_ = lean_array_get_size(v_es_4865_);
v___x_4870_ = lean_nat_dec_lt(v_j_4868_, v___x_4869_);
if (v___x_4870_ == 0)
{
lean_dec(v_j_4868_);
lean_dec(v_x_4864_);
lean_dec_ref(v_x_4863_);
return v_x_4860_;
}
else
{
lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4919_; 
lean_inc_ref(v_es_4865_);
v_isSharedCheck_4919_ = !lean_is_exclusive(v_x_4860_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; 
v_unused_4920_ = lean_ctor_get(v_x_4860_, 0);
lean_dec(v_unused_4920_);
v___x_4872_ = v_x_4860_;
v_isShared_4873_ = v_isSharedCheck_4919_;
goto v_resetjp_4871_;
}
else
{
lean_dec(v_x_4860_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4919_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v_v_4874_; lean_object* v___x_4875_; lean_object* v_xs_x27_4876_; lean_object* v___y_4878_; 
v_v_4874_ = lean_array_fget(v_es_4865_, v_j_4868_);
v___x_4875_ = lean_box(0);
v_xs_x27_4876_ = lean_array_fset(v_es_4865_, v_j_4868_, v___x_4875_);
switch(lean_obj_tag(v_v_4874_))
{
case 0:
{
lean_object* v_key_4883_; lean_object* v_val_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4904_; 
v_key_4883_ = lean_ctor_get(v_v_4874_, 0);
v_val_4884_ = lean_ctor_get(v_v_4874_, 1);
v_isSharedCheck_4904_ = !lean_is_exclusive(v_v_4874_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4886_ = v_v_4874_;
v_isShared_4887_ = v_isSharedCheck_4904_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_val_4884_);
lean_inc(v_key_4883_);
lean_dec(v_v_4874_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4904_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v_fst_4891_; lean_object* v_snd_4892_; lean_object* v_fst_4893_; lean_object* v_snd_4894_; size_t v___x_4895_; size_t v___x_4896_; uint8_t v___x_4897_; 
v_fst_4891_ = lean_ctor_get(v_x_4863_, 0);
v_snd_4892_ = lean_ctor_get(v_x_4863_, 1);
v_fst_4893_ = lean_ctor_get(v_key_4883_, 0);
v_snd_4894_ = lean_ctor_get(v_key_4883_, 1);
v___x_4895_ = lean_ptr_addr(v_fst_4891_);
v___x_4896_ = lean_ptr_addr(v_fst_4893_);
v___x_4897_ = lean_usize_dec_eq(v___x_4895_, v___x_4896_);
if (v___x_4897_ == 0)
{
lean_del_object(v___x_4886_);
goto v___jp_4888_;
}
else
{
size_t v___x_4898_; size_t v___x_4899_; uint8_t v___x_4900_; 
v___x_4898_ = lean_ptr_addr(v_snd_4892_);
v___x_4899_ = lean_ptr_addr(v_snd_4894_);
v___x_4900_ = lean_usize_dec_eq(v___x_4898_, v___x_4899_);
if (v___x_4900_ == 0)
{
lean_del_object(v___x_4886_);
goto v___jp_4888_;
}
else
{
lean_object* v___x_4902_; 
lean_dec(v_val_4884_);
lean_dec(v_key_4883_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 1, v_x_4864_);
lean_ctor_set(v___x_4886_, 0, v_x_4863_);
v___x_4902_ = v___x_4886_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_x_4863_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_x_4864_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
v___y_4878_ = v___x_4902_;
goto v___jp_4877_;
}
}
}
v___jp_4888_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4883_, v_val_4884_, v_x_4863_, v_x_4864_);
v___x_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
v___y_4878_ = v___x_4890_;
goto v___jp_4877_;
}
}
}
case 1:
{
lean_object* v_node_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4917_; 
v_node_4905_ = lean_ctor_get(v_v_4874_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v_v_4874_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4907_ = v_v_4874_;
v_isShared_4908_ = v_isSharedCheck_4917_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_node_4905_);
lean_dec(v_v_4874_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4917_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
size_t v___x_4909_; size_t v___x_4910_; size_t v___x_4911_; size_t v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4909_ = ((size_t)5ULL);
v___x_4910_ = lean_usize_shift_right(v_x_4861_, v___x_4909_);
v___x_4911_ = ((size_t)1ULL);
v___x_4912_ = lean_usize_add(v_x_4862_, v___x_4911_);
v___x_4913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4905_, v___x_4910_, v___x_4912_, v_x_4863_, v_x_4864_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4913_);
v___x_4915_ = v___x_4907_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4913_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
v___y_4878_ = v___x_4915_;
goto v___jp_4877_;
}
}
}
default: 
{
lean_object* v___x_4918_; 
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v_x_4863_);
lean_ctor_set(v___x_4918_, 1, v_x_4864_);
v___y_4878_ = v___x_4918_;
goto v___jp_4877_;
}
}
v___jp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4879_ = lean_array_fset(v_xs_x27_4876_, v_j_4868_, v___y_4878_);
lean_dec(v_j_4868_);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v___x_4879_);
v___x_4881_ = v___x_4872_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
}
else
{
lean_object* v_ks_4921_; lean_object* v_vs_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4940_; 
v_ks_4921_ = lean_ctor_get(v_x_4860_, 0);
v_vs_4922_ = lean_ctor_get(v_x_4860_, 1);
v_isSharedCheck_4940_ = !lean_is_exclusive(v_x_4860_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4924_ = v_x_4860_;
v_isShared_4925_ = v_isSharedCheck_4940_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_vs_4922_);
lean_inc(v_ks_4921_);
lean_dec(v_x_4860_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4940_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_ks_4921_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_vs_4922_);
v___x_4927_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v_newNode_4928_; size_t v___x_4929_; uint8_t v___x_4930_; 
v_newNode_4928_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4927_, v_x_4863_, v_x_4864_);
v___x_4929_ = ((size_t)7ULL);
v___x_4930_ = lean_usize_dec_le(v___x_4929_, v_x_4862_);
if (v___x_4930_ == 0)
{
lean_object* v___x_4931_; lean_object* v___x_4932_; uint8_t v___x_4933_; 
v___x_4931_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4928_);
v___x_4932_ = lean_unsigned_to_nat(4u);
v___x_4933_ = lean_nat_dec_lt(v___x_4931_, v___x_4932_);
lean_dec(v___x_4931_);
if (v___x_4933_ == 0)
{
lean_object* v_ks_4934_; lean_object* v_vs_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v_ks_4934_ = lean_ctor_get(v_newNode_4928_, 0);
lean_inc_ref(v_ks_4934_);
v_vs_4935_ = lean_ctor_get(v_newNode_4928_, 1);
lean_inc_ref(v_vs_4935_);
lean_dec_ref(v_newNode_4928_);
v___x_4936_ = lean_unsigned_to_nat(0u);
v___x_4937_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0);
v___x_4938_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4862_, v_ks_4934_, v_vs_4935_, v___x_4936_, v___x_4937_);
lean_dec_ref(v_vs_4935_);
lean_dec_ref(v_ks_4934_);
return v___x_4938_;
}
else
{
return v_newNode_4928_;
}
}
else
{
return v_newNode_4928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4941_, lean_object* v_keys_4942_, lean_object* v_vals_4943_, lean_object* v_i_4944_, lean_object* v_entries_4945_){
_start:
{
lean_object* v___x_4946_; uint8_t v___x_4947_; 
v___x_4946_ = lean_array_get_size(v_keys_4942_);
v___x_4947_ = lean_nat_dec_lt(v_i_4944_, v___x_4946_);
if (v___x_4947_ == 0)
{
lean_dec(v_i_4944_);
return v_entries_4945_;
}
else
{
lean_object* v_k_4948_; lean_object* v_fst_4949_; lean_object* v_snd_4950_; lean_object* v_v_4951_; size_t v___x_4952_; size_t v___x_4953_; size_t v___x_4954_; uint64_t v___x_4955_; size_t v___x_4956_; size_t v___x_4957_; uint64_t v___x_4958_; uint64_t v___x_4959_; size_t v_h_4960_; size_t v___x_4961_; lean_object* v___x_4962_; size_t v___x_4963_; size_t v___x_4964_; size_t v___x_4965_; size_t v_h_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_k_4948_ = lean_array_fget_borrowed(v_keys_4942_, v_i_4944_);
v_fst_4949_ = lean_ctor_get(v_k_4948_, 0);
v_snd_4950_ = lean_ctor_get(v_k_4948_, 1);
v_v_4951_ = lean_array_fget_borrowed(v_vals_4943_, v_i_4944_);
v___x_4952_ = lean_ptr_addr(v_fst_4949_);
v___x_4953_ = ((size_t)3ULL);
v___x_4954_ = lean_usize_shift_right(v___x_4952_, v___x_4953_);
v___x_4955_ = lean_usize_to_uint64(v___x_4954_);
v___x_4956_ = lean_ptr_addr(v_snd_4950_);
v___x_4957_ = lean_usize_shift_right(v___x_4956_, v___x_4953_);
v___x_4958_ = lean_usize_to_uint64(v___x_4957_);
v___x_4959_ = lean_uint64_mix_hash(v___x_4955_, v___x_4958_);
v_h_4960_ = lean_uint64_to_usize(v___x_4959_);
v___x_4961_ = ((size_t)5ULL);
v___x_4962_ = lean_unsigned_to_nat(1u);
v___x_4963_ = ((size_t)1ULL);
v___x_4964_ = lean_usize_sub(v_depth_4941_, v___x_4963_);
v___x_4965_ = lean_usize_mul(v___x_4961_, v___x_4964_);
v_h_4966_ = lean_usize_shift_right(v_h_4960_, v___x_4965_);
v___x_4967_ = lean_nat_add(v_i_4944_, v___x_4962_);
lean_dec(v_i_4944_);
lean_inc(v_v_4951_);
lean_inc(v_k_4948_);
v___x_4968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4945_, v_h_4966_, v_depth_4941_, v_k_4948_, v_v_4951_);
v_i_4944_ = v___x_4967_;
v_entries_4945_ = v___x_4968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4970_, lean_object* v_keys_4971_, lean_object* v_vals_4972_, lean_object* v_i_4973_, lean_object* v_entries_4974_){
_start:
{
size_t v_depth_boxed_4975_; lean_object* v_res_4976_; 
v_depth_boxed_4975_ = lean_unbox_usize(v_depth_4970_);
lean_dec(v_depth_4970_);
v_res_4976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4975_, v_keys_4971_, v_vals_4972_, v_i_4973_, v_entries_4974_);
lean_dec_ref(v_vals_4972_);
lean_dec_ref(v_keys_4971_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4977_, lean_object* v_x_4978_, lean_object* v_x_4979_, lean_object* v_x_4980_, lean_object* v_x_4981_){
_start:
{
size_t v_x_3110__boxed_4982_; size_t v_x_3111__boxed_4983_; lean_object* v_res_4984_; 
v_x_3110__boxed_4982_ = lean_unbox_usize(v_x_4978_);
lean_dec(v_x_4978_);
v_x_3111__boxed_4983_ = lean_unbox_usize(v_x_4979_);
lean_dec(v_x_4979_);
v_res_4984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4977_, v_x_3110__boxed_4982_, v_x_3111__boxed_4983_, v_x_4980_, v_x_4981_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4985_, lean_object* v_x_4986_, lean_object* v_x_4987_){
_start:
{
lean_object* v_fst_4988_; lean_object* v_snd_4989_; size_t v___x_4990_; size_t v___x_4991_; size_t v___x_4992_; uint64_t v___x_4993_; size_t v___x_4994_; size_t v___x_4995_; uint64_t v___x_4996_; uint64_t v___x_4997_; size_t v___x_4998_; size_t v___x_4999_; lean_object* v___x_5000_; 
v_fst_4988_ = lean_ctor_get(v_x_4986_, 0);
v_snd_4989_ = lean_ctor_get(v_x_4986_, 1);
v___x_4990_ = lean_ptr_addr(v_fst_4988_);
v___x_4991_ = ((size_t)3ULL);
v___x_4992_ = lean_usize_shift_right(v___x_4990_, v___x_4991_);
v___x_4993_ = lean_usize_to_uint64(v___x_4992_);
v___x_4994_ = lean_ptr_addr(v_snd_4989_);
v___x_4995_ = lean_usize_shift_right(v___x_4994_, v___x_4991_);
v___x_4996_ = lean_usize_to_uint64(v___x_4995_);
v___x_4997_ = lean_uint64_mix_hash(v___x_4993_, v___x_4996_);
v___x_4998_ = lean_uint64_to_usize(v___x_4997_);
v___x_4999_ = ((size_t)1ULL);
v___x_5000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4985_, v___x_4998_, v___x_4999_, v_x_4986_, v_x_4987_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_5001_, lean_object* v_t_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v_key_5009_; lean_object* v___x_5010_; lean_object* v_defEqI_5011_; lean_object* v___x_5012_; 
lean_inc_ref(v_t_5002_);
lean_inc_ref(v_s_5001_);
v_key_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_5009_, 0, v_s_5001_);
lean_ctor_set(v_key_5009_, 1, v_t_5002_);
v___x_5010_ = lean_st_ref_get(v_a_5003_);
v_defEqI_5011_ = lean_ctor_get(v___x_5010_, 8);
lean_inc_ref(v_defEqI_5011_);
lean_dec(v___x_5010_);
v___x_5012_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_5011_, v_key_5009_);
lean_dec_ref(v_defEqI_5011_);
if (lean_obj_tag(v___x_5012_) == 1)
{
lean_object* v_val_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec_ref_known(v_key_5009_, 2);
lean_dec_ref(v_t_5002_);
lean_dec_ref(v_s_5001_);
v_val_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_val_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
lean_ctor_set_tag(v___x_5015_, 0);
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_val_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
else
{
lean_object* v___x_5021_; 
lean_dec(v___x_5012_);
v___x_5021_ = l_Lean_Meta_isDefEqI(v_s_5001_, v_t_5002_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5053_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5024_ = v___x_5021_;
v_isShared_5025_ = v_isSharedCheck_5053_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5053_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v_share_5027_; lean_object* v_maxFVar_5028_; lean_object* v_proofInstInfo_5029_; lean_object* v_proofInstInfoFVar_5030_; lean_object* v_letValue_5031_; lean_object* v_inferType_5032_; lean_object* v_getLevel_5033_; lean_object* v_congrInfo_5034_; lean_object* v_defEqI_5035_; lean_object* v_extensions_5036_; lean_object* v_issues_5037_; lean_object* v_canon_5038_; lean_object* v_instanceOverrides_5039_; uint8_t v_debug_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5052_; 
v___x_5026_ = lean_st_ref_take(v_a_5003_);
v_share_5027_ = lean_ctor_get(v___x_5026_, 0);
v_maxFVar_5028_ = lean_ctor_get(v___x_5026_, 1);
v_proofInstInfo_5029_ = lean_ctor_get(v___x_5026_, 2);
v_proofInstInfoFVar_5030_ = lean_ctor_get(v___x_5026_, 3);
v_letValue_5031_ = lean_ctor_get(v___x_5026_, 4);
v_inferType_5032_ = lean_ctor_get(v___x_5026_, 5);
v_getLevel_5033_ = lean_ctor_get(v___x_5026_, 6);
v_congrInfo_5034_ = lean_ctor_get(v___x_5026_, 7);
v_defEqI_5035_ = lean_ctor_get(v___x_5026_, 8);
v_extensions_5036_ = lean_ctor_get(v___x_5026_, 9);
v_issues_5037_ = lean_ctor_get(v___x_5026_, 10);
v_canon_5038_ = lean_ctor_get(v___x_5026_, 11);
v_instanceOverrides_5039_ = lean_ctor_get(v___x_5026_, 12);
v_debug_5040_ = lean_ctor_get_uint8(v___x_5026_, sizeof(void*)*13);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5042_ = v___x_5026_;
v_isShared_5043_ = v_isSharedCheck_5052_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_instanceOverrides_5039_);
lean_inc(v_canon_5038_);
lean_inc(v_issues_5037_);
lean_inc(v_extensions_5036_);
lean_inc(v_defEqI_5035_);
lean_inc(v_congrInfo_5034_);
lean_inc(v_getLevel_5033_);
lean_inc(v_inferType_5032_);
lean_inc(v_letValue_5031_);
lean_inc(v_proofInstInfoFVar_5030_);
lean_inc(v_proofInstInfo_5029_);
lean_inc(v_maxFVar_5028_);
lean_inc(v_share_5027_);
lean_dec(v___x_5026_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5052_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5044_; lean_object* v___x_5046_; 
lean_inc(v_a_5022_);
v___x_5044_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_5035_, v_key_5009_, v_a_5022_);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 8, v___x_5044_);
v___x_5046_ = v___x_5042_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_share_5027_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v_maxFVar_5028_);
lean_ctor_set(v_reuseFailAlloc_5051_, 2, v_proofInstInfo_5029_);
lean_ctor_set(v_reuseFailAlloc_5051_, 3, v_proofInstInfoFVar_5030_);
lean_ctor_set(v_reuseFailAlloc_5051_, 4, v_letValue_5031_);
lean_ctor_set(v_reuseFailAlloc_5051_, 5, v_inferType_5032_);
lean_ctor_set(v_reuseFailAlloc_5051_, 6, v_getLevel_5033_);
lean_ctor_set(v_reuseFailAlloc_5051_, 7, v_congrInfo_5034_);
lean_ctor_set(v_reuseFailAlloc_5051_, 8, v___x_5044_);
lean_ctor_set(v_reuseFailAlloc_5051_, 9, v_extensions_5036_);
lean_ctor_set(v_reuseFailAlloc_5051_, 10, v_issues_5037_);
lean_ctor_set(v_reuseFailAlloc_5051_, 11, v_canon_5038_);
lean_ctor_set(v_reuseFailAlloc_5051_, 12, v_instanceOverrides_5039_);
lean_ctor_set_uint8(v_reuseFailAlloc_5051_, sizeof(void*)*13, v_debug_5040_);
v___x_5046_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5047_; lean_object* v___x_5049_; 
v___x_5047_ = lean_st_ref_put(v_a_5003_, v___x_5046_);
if (v_isShared_5025_ == 0)
{
v___x_5049_ = v___x_5024_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5022_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_5009_, 2);
return v___x_5021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_5054_, lean_object* v_t_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_5054_, v_t_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_5063_, lean_object* v_t_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v___x_5072_; 
v___x_5072_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_5063_, v_t_5064_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_5073_, lean_object* v_t_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_Meta_Sym_isDefEqI(v_s_5073_, v_t_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec_ref(v_a_5075_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_5083_, lean_object* v_x_5084_, lean_object* v_x_5085_){
_start:
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_5084_, v_x_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_5087_, lean_object* v_x_5088_, lean_object* v_x_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_5087_, v_x_5088_, v_x_5089_);
lean_dec_ref(v_x_5089_);
lean_dec_ref(v_x_5088_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_5091_, lean_object* v_x_5092_, lean_object* v_x_5093_, lean_object* v_x_5094_){
_start:
{
lean_object* v___x_5095_; 
v___x_5095_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_5092_, v_x_5093_, v_x_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_5096_, lean_object* v_x_5097_, size_t v_x_5098_, lean_object* v_x_5099_){
_start:
{
lean_object* v___x_5100_; 
v___x_5100_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_5097_, v_x_5098_, v_x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5101_, lean_object* v_x_5102_, lean_object* v_x_5103_, lean_object* v_x_5104_){
_start:
{
size_t v_x_3405__boxed_5105_; lean_object* v_res_5106_; 
v_x_3405__boxed_5105_ = lean_unbox_usize(v_x_5103_);
lean_dec(v_x_5103_);
v_res_5106_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_5101_, v_x_5102_, v_x_3405__boxed_5105_, v_x_5104_);
lean_dec_ref(v_x_5104_);
lean_dec_ref(v_x_5102_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_5107_, lean_object* v_x_5108_, size_t v_x_5109_, size_t v_x_5110_, lean_object* v_x_5111_, lean_object* v_x_5112_){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_5108_, v_x_5109_, v_x_5110_, v_x_5111_, v_x_5112_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5114_, lean_object* v_x_5115_, lean_object* v_x_5116_, lean_object* v_x_5117_, lean_object* v_x_5118_, lean_object* v_x_5119_){
_start:
{
size_t v_x_3416__boxed_5120_; size_t v_x_3417__boxed_5121_; lean_object* v_res_5122_; 
v_x_3416__boxed_5120_ = lean_unbox_usize(v_x_5116_);
lean_dec(v_x_5116_);
v_x_3417__boxed_5121_ = lean_unbox_usize(v_x_5117_);
lean_dec(v_x_5117_);
v_res_5122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_5114_, v_x_5115_, v_x_3416__boxed_5120_, v_x_3417__boxed_5121_, v_x_5118_, v_x_5119_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5123_, lean_object* v_keys_5124_, lean_object* v_vals_5125_, lean_object* v_heq_5126_, lean_object* v_i_5127_, lean_object* v_k_5128_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_5124_, v_vals_5125_, v_i_5127_, v_k_5128_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5130_, lean_object* v_keys_5131_, lean_object* v_vals_5132_, lean_object* v_heq_5133_, lean_object* v_i_5134_, lean_object* v_k_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_5130_, v_keys_5131_, v_vals_5132_, v_heq_5133_, v_i_5134_, v_k_5135_);
lean_dec_ref(v_k_5135_);
lean_dec_ref(v_vals_5132_);
lean_dec_ref(v_keys_5131_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_5137_, lean_object* v_n_5138_, lean_object* v_k_5139_, lean_object* v_v_5140_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_5138_, v_k_5139_, v_v_5140_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_5142_, size_t v_depth_5143_, lean_object* v_keys_5144_, lean_object* v_vals_5145_, lean_object* v_heq_5146_, lean_object* v_i_5147_, lean_object* v_entries_5148_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_5143_, v_keys_5144_, v_vals_5145_, v_i_5147_, v_entries_5148_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_5150_, lean_object* v_depth_5151_, lean_object* v_keys_5152_, lean_object* v_vals_5153_, lean_object* v_heq_5154_, lean_object* v_i_5155_, lean_object* v_entries_5156_){
_start:
{
size_t v_depth_boxed_5157_; lean_object* v_res_5158_; 
v_depth_boxed_5157_ = lean_unbox_usize(v_depth_5151_);
lean_dec(v_depth_5151_);
v_res_5158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_5150_, v_depth_boxed_5157_, v_keys_5152_, v_vals_5153_, v_heq_5154_, v_i_5155_, v_entries_5156_);
lean_dec_ref(v_vals_5153_);
lean_dec_ref(v_keys_5152_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_5159_, lean_object* v_x_5160_, lean_object* v_x_5161_, lean_object* v_x_5162_, lean_object* v_x_5163_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_5160_, v_x_5161_, v_x_5162_, v_x_5163_);
return v___x_5164_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0(void){
_start:
{
lean_object* v___x_5165_; lean_object* v___f_5166_; 
v___x_5165_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_5166_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5166_, 0, v___x_5165_);
return v___f_5166_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1(void){
_start:
{
lean_object* v___x_5167_; lean_object* v___f_5168_; 
v___x_5167_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_5168_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5168_, 0, v___x_5167_);
return v___f_5168_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2(void){
_start:
{
lean_object* v___f_5169_; lean_object* v___f_5170_; lean_object* v___x_5171_; 
v___f_5169_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1);
v___f_5170_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0);
v___x_5171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___f_5170_);
lean_ctor_set(v___x_5171_, 1, v___f_5169_);
return v___x_5171_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3(void){
_start:
{
lean_object* v___x_5172_; lean_object* v___f_5173_; 
v___x_5172_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_5173_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5173_, 0, v___x_5172_);
return v___f_5173_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4(void){
_start:
{
lean_object* v___x_5174_; lean_object* v___f_5175_; 
v___x_5174_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_5175_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5175_, 0, v___x_5174_);
return v___f_5175_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5(void){
_start:
{
lean_object* v___f_5176_; lean_object* v___f_5177_; lean_object* v___x_5178_; 
v___f_5176_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4);
v___f_5177_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3);
v___x_5178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5178_, 0, v___f_5177_);
lean_ctor_set(v___x_5178_, 1, v___f_5176_);
return v___x_5178_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6(void){
_start:
{
lean_object* v___x_5179_; lean_object* v___f_5180_; 
v___x_5179_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_5180_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5180_, 0, v___x_5179_);
return v___f_5180_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7(void){
_start:
{
lean_object* v___x_5181_; lean_object* v___f_5182_; 
v___x_5181_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_5182_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5182_, 0, v___x_5181_);
return v___f_5182_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8(void){
_start:
{
lean_object* v___f_5183_; lean_object* v___f_5184_; lean_object* v___x_5185_; 
v___f_5183_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7);
v___f_5184_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6);
v___x_5185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5185_, 0, v___f_5184_);
lean_ctor_set(v___x_5185_, 1, v___f_5183_);
return v___x_5185_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9(void){
_start:
{
lean_object* v___x_5186_; lean_object* v___f_5187_; 
v___x_5186_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_5187_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5187_, 0, v___x_5186_);
return v___f_5187_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10(void){
_start:
{
lean_object* v___x_5188_; lean_object* v___f_5189_; 
v___x_5188_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_5189_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5189_, 0, v___x_5188_);
return v___f_5189_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11(void){
_start:
{
lean_object* v___f_5190_; lean_object* v___f_5191_; lean_object* v___x_5192_; 
v___f_5190_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10);
v___f_5191_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9);
v___x_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___f_5191_);
lean_ctor_set(v___x_5192_, 1, v___f_5190_);
return v___x_5192_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16(void){
_start:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___x_5197_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_5198_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5199_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_5200_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_5199_, v___x_5198_, v___x_5197_);
return v___x_5200_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17(void){
_start:
{
lean_object* v___x_5201_; lean_object* v___f_5202_; lean_object* v___f_5203_; lean_object* v___x_5204_; 
v___x_5201_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16);
v___f_5202_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5203_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_5204_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_5203_, v___f_5202_, v___x_5201_);
return v___x_5204_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18(void){
_start:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5205_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17);
v___x_5206_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5207_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_5208_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_5207_, v___x_5206_, v___x_5205_);
return v___x_5208_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19(void){
_start:
{
lean_object* v___x_5209_; lean_object* v___f_5210_; lean_object* v___f_5211_; lean_object* v___x_5212_; 
v___x_5209_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18);
v___f_5210_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5211_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_5212_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_5211_, v___f_5210_, v___x_5209_);
return v___x_5212_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20(void){
_start:
{
lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___f_5215_; 
v___x_5213_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5214_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_5215_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5215_, 0, v___x_5214_);
lean_closure_set(v___f_5215_, 1, v___x_5213_);
return v___f_5215_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21(void){
_start:
{
lean_object* v___f_5216_; lean_object* v___f_5217_; lean_object* v___f_5218_; 
v___f_5216_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5217_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20);
v___f_5218_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5218_, 0, v___f_5217_);
lean_closure_set(v___f_5218_, 1, v___f_5216_);
return v___f_5218_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23(void){
_start:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5220_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22));
v___x_5221_ = l_Lean_stringToMessageData(v___x_5220_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg(){
_start:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v_toApplicative_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5292_; 
v___x_5223_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_5224_ = l_StateRefT_x27_instMonad___redArg(v___x_5223_);
v_toApplicative_5225_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5292_ == 0)
{
lean_object* v_unused_5293_; 
v_unused_5293_ = lean_ctor_get(v___x_5224_, 1);
lean_dec(v_unused_5293_);
v___x_5227_ = v___x_5224_;
v_isShared_5228_ = v_isSharedCheck_5292_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_toApplicative_5225_);
lean_dec(v___x_5224_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5292_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v_toFunctor_5229_; lean_object* v_toSeq_5230_; lean_object* v_toSeqLeft_5231_; lean_object* v_toSeqRight_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5290_; 
v_toFunctor_5229_ = lean_ctor_get(v_toApplicative_5225_, 0);
v_toSeq_5230_ = lean_ctor_get(v_toApplicative_5225_, 2);
v_toSeqLeft_5231_ = lean_ctor_get(v_toApplicative_5225_, 3);
v_toSeqRight_5232_ = lean_ctor_get(v_toApplicative_5225_, 4);
v_isSharedCheck_5290_ = !lean_is_exclusive(v_toApplicative_5225_);
if (v_isSharedCheck_5290_ == 0)
{
lean_object* v_unused_5291_; 
v_unused_5291_ = lean_ctor_get(v_toApplicative_5225_, 1);
lean_dec(v_unused_5291_);
v___x_5234_ = v_toApplicative_5225_;
v_isShared_5235_ = v_isSharedCheck_5290_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_toSeqRight_5232_);
lean_inc(v_toSeqLeft_5231_);
lean_inc(v_toSeq_5230_);
lean_inc(v_toFunctor_5229_);
lean_dec(v_toApplicative_5225_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5290_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___f_5236_; lean_object* v___f_5237_; lean_object* v___f_5238_; lean_object* v___f_5239_; lean_object* v___x_5240_; lean_object* v___f_5241_; lean_object* v___f_5242_; lean_object* v___f_5243_; lean_object* v___x_5245_; 
v___f_5236_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_5237_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_5229_);
v___f_5238_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5238_, 0, v_toFunctor_5229_);
v___f_5239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5239_, 0, v_toFunctor_5229_);
v___x_5240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5240_, 0, v___f_5238_);
lean_ctor_set(v___x_5240_, 1, v___f_5239_);
v___f_5241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5241_, 0, v_toSeqRight_5232_);
v___f_5242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5242_, 0, v_toSeqLeft_5231_);
v___f_5243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5243_, 0, v_toSeq_5230_);
if (v_isShared_5235_ == 0)
{
lean_ctor_set(v___x_5234_, 4, v___f_5241_);
lean_ctor_set(v___x_5234_, 3, v___f_5242_);
lean_ctor_set(v___x_5234_, 2, v___f_5243_);
lean_ctor_set(v___x_5234_, 1, v___f_5236_);
lean_ctor_set(v___x_5234_, 0, v___x_5240_);
v___x_5245_ = v___x_5234_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v___x_5240_);
lean_ctor_set(v_reuseFailAlloc_5289_, 1, v___f_5236_);
lean_ctor_set(v_reuseFailAlloc_5289_, 2, v___f_5243_);
lean_ctor_set(v_reuseFailAlloc_5289_, 3, v___f_5242_);
lean_ctor_set(v_reuseFailAlloc_5289_, 4, v___f_5241_);
v___x_5245_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
lean_object* v___x_5247_; 
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 1, v___f_5237_);
lean_ctor_set(v___x_5227_, 0, v___x_5245_);
v___x_5247_ = v___x_5227_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5288_, 1, v___f_5237_);
v___x_5247_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5248_; lean_object* v_toApplicative_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5286_; 
v___x_5248_ = l_StateRefT_x27_instMonad___redArg(v___x_5247_);
v_toApplicative_5249_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5286_ == 0)
{
lean_object* v_unused_5287_; 
v_unused_5287_ = lean_ctor_get(v___x_5248_, 1);
lean_dec(v_unused_5287_);
v___x_5251_ = v___x_5248_;
v_isShared_5252_ = v_isSharedCheck_5286_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_toApplicative_5249_);
lean_dec(v___x_5248_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5286_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v_toFunctor_5253_; lean_object* v_toSeq_5254_; lean_object* v_toSeqLeft_5255_; lean_object* v_toSeqRight_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5284_; 
v_toFunctor_5253_ = lean_ctor_get(v_toApplicative_5249_, 0);
v_toSeq_5254_ = lean_ctor_get(v_toApplicative_5249_, 2);
v_toSeqLeft_5255_ = lean_ctor_get(v_toApplicative_5249_, 3);
v_toSeqRight_5256_ = lean_ctor_get(v_toApplicative_5249_, 4);
v_isSharedCheck_5284_ = !lean_is_exclusive(v_toApplicative_5249_);
if (v_isSharedCheck_5284_ == 0)
{
lean_object* v_unused_5285_; 
v_unused_5285_ = lean_ctor_get(v_toApplicative_5249_, 1);
lean_dec(v_unused_5285_);
v___x_5258_ = v_toApplicative_5249_;
v_isShared_5259_ = v_isSharedCheck_5284_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_toSeqRight_5256_);
lean_inc(v_toSeqLeft_5255_);
lean_inc(v_toSeq_5254_);
lean_inc(v_toFunctor_5253_);
lean_dec(v_toApplicative_5249_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5284_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___f_5260_; lean_object* v___f_5261_; lean_object* v___f_5262_; lean_object* v___f_5263_; lean_object* v___x_5264_; lean_object* v___f_5265_; lean_object* v___f_5266_; lean_object* v___f_5267_; lean_object* v___x_5269_; 
v___f_5260_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_5261_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_5253_);
v___f_5262_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5262_, 0, v_toFunctor_5253_);
v___f_5263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5263_, 0, v_toFunctor_5253_);
v___x_5264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___f_5262_);
lean_ctor_set(v___x_5264_, 1, v___f_5263_);
v___f_5265_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5265_, 0, v_toSeqRight_5256_);
v___f_5266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5266_, 0, v_toSeqLeft_5255_);
v___f_5267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5267_, 0, v_toSeq_5254_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 4, v___f_5265_);
lean_ctor_set(v___x_5258_, 3, v___f_5266_);
lean_ctor_set(v___x_5258_, 2, v___f_5267_);
lean_ctor_set(v___x_5258_, 1, v___f_5260_);
lean_ctor_set(v___x_5258_, 0, v___x_5264_);
v___x_5269_ = v___x_5258_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5264_);
lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___f_5260_);
lean_ctor_set(v_reuseFailAlloc_5283_, 2, v___f_5267_);
lean_ctor_set(v_reuseFailAlloc_5283_, 3, v___f_5266_);
lean_ctor_set(v_reuseFailAlloc_5283_, 4, v___f_5265_);
v___x_5269_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
lean_object* v___x_5271_; 
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 1, v___f_5261_);
lean_ctor_set(v___x_5251_, 0, v___x_5269_);
v___x_5271_ = v___x_5251_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5269_);
lean_ctor_set(v_reuseFailAlloc_5282_, 1, v___f_5261_);
v___x_5271_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v_toMonadRef_5276_; lean_object* v___f_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5272_ = l_StateRefT_x27_instMonad___redArg(v___x_5271_);
v___x_5273_ = l_ReaderT_instMonad___redArg(v___x_5272_);
v___x_5274_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11);
v___x_5275_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19);
v_toMonadRef_5276_ = lean_ctor_get(v___x_5275_, 0);
v___f_5277_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21);
lean_inc_ref(v___x_5273_);
v___x_5278_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_5277_, v___x_5273_);
lean_inc_ref(v_toMonadRef_5276_);
v___x_5279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5274_);
lean_ctor_set(v___x_5279_, 1, v_toMonadRef_5276_);
lean_ctor_set(v___x_5279_, 2, v___x_5278_);
v___x_5280_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23);
v___x_5281_ = l_Lean_throwError___redArg(v___x_5273_, v___x_5279_, v___x_5280_);
return v___x_5281_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object* v___dummy_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v_res_5295_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_5296_; 
v___x_5296_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_5297_){
_start:
{
lean_object* v___x_5298_; 
v___x_5298_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_5299_, lean_object* v_extensions_5300_){
_start:
{
lean_object* v_id_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; 
v_id_5302_ = lean_ctor_get(v_ext_5299_, 0);
v___x_5303_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_5304_ = lean_array_get_borrowed(v___x_5303_, v_extensions_5300_, v_id_5302_);
lean_inc(v___x_5304_);
v___x_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5304_);
return v___x_5305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_5306_, lean_object* v_extensions_5307_, lean_object* v_a_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5306_, v_extensions_5307_);
lean_dec_ref(v_extensions_5307_);
lean_dec_ref(v_ext_5306_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_5310_, lean_object* v_ext_5311_, lean_object* v_extensions_5312_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5311_, v_extensions_5312_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_5315_, lean_object* v_ext_5316_, lean_object* v_extensions_5317_, lean_object* v_a_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_5315_, v_ext_5316_, v_extensions_5317_);
lean_dec_ref(v_extensions_5317_);
lean_dec_ref(v_ext_5316_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_){
_start:
{
lean_object* v___x_5324_; lean_object* v_extensions_5325_; lean_object* v_ref_5326_; lean_object* v___x_5327_; 
v___x_5324_ = lean_st_ref_get(v_a_5321_);
v_extensions_5325_ = lean_ctor_get(v___x_5324_, 9);
lean_inc_ref(v_extensions_5325_);
lean_dec(v___x_5324_);
v_ref_5326_ = lean_ctor_get(v_a_5322_, 2);
v___x_5327_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5320_, v_extensions_5325_);
lean_dec_ref(v_extensions_5325_);
if (lean_obj_tag(v___x_5327_) == 0)
{
lean_object* v_a_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5335_; 
v_a_5328_ = lean_ctor_get(v___x_5327_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5330_ = v___x_5327_;
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_a_5328_);
lean_dec(v___x_5327_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5333_; 
if (v_isShared_5331_ == 0)
{
v___x_5333_ = v___x_5330_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
else
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5347_; 
v_a_5336_ = lean_ctor_get(v___x_5327_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5338_ = v___x_5327_;
v_isShared_5339_ = v_isSharedCheck_5347_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5327_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5347_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5345_; 
v___x_5340_ = lean_io_error_to_string(v_a_5336_);
v___x_5341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
v___x_5342_ = l_Lean_MessageData_ofFormat(v___x_5341_);
lean_inc(v_ref_5326_);
v___x_5343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5343_, 0, v_ref_5326_);
lean_ctor_set(v___x_5343_, 1, v___x_5342_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5343_);
v___x_5345_ = v___x_5338_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5348_, v_a_5349_, v_a_5350_);
lean_dec_ref(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec_ref(v_ext_5348_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_5353_, lean_object* v_ext_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5354_, v_a_5356_, v_a_5359_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_5363_, lean_object* v_ext_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_5363_, v_ext_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_);
lean_dec(v_a_5370_);
lean_dec_ref(v_a_5369_);
lean_dec(v_a_5368_);
lean_dec_ref(v_a_5367_);
lean_dec(v_a_5366_);
lean_dec_ref(v_a_5365_);
lean_dec_ref(v_ext_5364_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_5373_, lean_object* v_f_5374_, lean_object* v_a_5375_){
_start:
{
lean_object* v___x_5377_; lean_object* v_share_5378_; lean_object* v_maxFVar_5379_; lean_object* v_proofInstInfo_5380_; lean_object* v_proofInstInfoFVar_5381_; lean_object* v_letValue_5382_; lean_object* v_inferType_5383_; lean_object* v_getLevel_5384_; lean_object* v_congrInfo_5385_; lean_object* v_defEqI_5386_; lean_object* v_extensions_5387_; lean_object* v_issues_5388_; lean_object* v_canon_5389_; lean_object* v_instanceOverrides_5390_; uint8_t v_debug_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5410_; 
v___x_5377_ = lean_st_ref_take(v_a_5375_);
v_share_5378_ = lean_ctor_get(v___x_5377_, 0);
v_maxFVar_5379_ = lean_ctor_get(v___x_5377_, 1);
v_proofInstInfo_5380_ = lean_ctor_get(v___x_5377_, 2);
v_proofInstInfoFVar_5381_ = lean_ctor_get(v___x_5377_, 3);
v_letValue_5382_ = lean_ctor_get(v___x_5377_, 4);
v_inferType_5383_ = lean_ctor_get(v___x_5377_, 5);
v_getLevel_5384_ = lean_ctor_get(v___x_5377_, 6);
v_congrInfo_5385_ = lean_ctor_get(v___x_5377_, 7);
v_defEqI_5386_ = lean_ctor_get(v___x_5377_, 8);
v_extensions_5387_ = lean_ctor_get(v___x_5377_, 9);
v_issues_5388_ = lean_ctor_get(v___x_5377_, 10);
v_canon_5389_ = lean_ctor_get(v___x_5377_, 11);
v_instanceOverrides_5390_ = lean_ctor_get(v___x_5377_, 12);
v_debug_5391_ = lean_ctor_get_uint8(v___x_5377_, sizeof(void*)*13);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5393_ = v___x_5377_;
v_isShared_5394_ = v_isSharedCheck_5410_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_instanceOverrides_5390_);
lean_inc(v_canon_5389_);
lean_inc(v_issues_5388_);
lean_inc(v_extensions_5387_);
lean_inc(v_defEqI_5386_);
lean_inc(v_congrInfo_5385_);
lean_inc(v_getLevel_5384_);
lean_inc(v_inferType_5383_);
lean_inc(v_letValue_5382_);
lean_inc(v_proofInstInfoFVar_5381_);
lean_inc(v_proofInstInfo_5380_);
lean_inc(v_maxFVar_5379_);
lean_inc(v_share_5378_);
lean_dec(v___x_5377_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5410_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v_id_5395_; lean_object* v___x_5396_; lean_object* v___y_5398_; lean_object* v___x_5404_; uint8_t v___x_5405_; 
v_id_5395_ = lean_ctor_get(v_ext_5373_, 0);
v___x_5396_ = lean_box(0);
v___x_5404_ = lean_array_get_size(v_extensions_5387_);
v___x_5405_ = lean_nat_dec_lt(v_id_5395_, v___x_5404_);
if (v___x_5405_ == 0)
{
lean_dec(v_f_5374_);
v___y_5398_ = v_extensions_5387_;
goto v___jp_5397_;
}
else
{
lean_object* v_v_5406_; lean_object* v_xs_x27_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
v_v_5406_ = lean_array_fget(v_extensions_5387_, v_id_5395_);
v_xs_x27_5407_ = lean_array_fset(v_extensions_5387_, v_id_5395_, v___x_5396_);
v___x_5408_ = lean_apply_1(v_f_5374_, v_v_5406_);
v___x_5409_ = lean_array_fset(v_xs_x27_5407_, v_id_5395_, v___x_5408_);
v___y_5398_ = v___x_5409_;
goto v___jp_5397_;
}
v___jp_5397_:
{
lean_object* v___x_5400_; 
if (v_isShared_5394_ == 0)
{
lean_ctor_set(v___x_5393_, 9, v___y_5398_);
v___x_5400_ = v___x_5393_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_share_5378_);
lean_ctor_set(v_reuseFailAlloc_5403_, 1, v_maxFVar_5379_);
lean_ctor_set(v_reuseFailAlloc_5403_, 2, v_proofInstInfo_5380_);
lean_ctor_set(v_reuseFailAlloc_5403_, 3, v_proofInstInfoFVar_5381_);
lean_ctor_set(v_reuseFailAlloc_5403_, 4, v_letValue_5382_);
lean_ctor_set(v_reuseFailAlloc_5403_, 5, v_inferType_5383_);
lean_ctor_set(v_reuseFailAlloc_5403_, 6, v_getLevel_5384_);
lean_ctor_set(v_reuseFailAlloc_5403_, 7, v_congrInfo_5385_);
lean_ctor_set(v_reuseFailAlloc_5403_, 8, v_defEqI_5386_);
lean_ctor_set(v_reuseFailAlloc_5403_, 9, v___y_5398_);
lean_ctor_set(v_reuseFailAlloc_5403_, 10, v_issues_5388_);
lean_ctor_set(v_reuseFailAlloc_5403_, 11, v_canon_5389_);
lean_ctor_set(v_reuseFailAlloc_5403_, 12, v_instanceOverrides_5390_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, sizeof(void*)*13, v_debug_5391_);
v___x_5400_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5401_ = lean_st_ref_put(v_a_5375_, v___x_5400_);
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5396_);
return v___x_5402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_5411_, lean_object* v_f_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_res_5415_; 
v_res_5415_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5411_, v_f_5412_, v_a_5413_);
lean_dec(v_a_5413_);
lean_dec_ref(v_ext_5411_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_5416_, lean_object* v_ext_5417_, lean_object* v_f_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_){
_start:
{
lean_object* v___x_5426_; 
v___x_5426_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5417_, v_f_5418_, v_a_5420_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5427_, lean_object* v_ext_5428_, lean_object* v_f_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5427_, v_ext_5428_, v_f_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
lean_dec(v_a_5433_);
lean_dec_ref(v_a_5432_);
lean_dec(v_a_5431_);
lean_dec_ref(v_a_5430_);
lean_dec_ref(v_ext_5428_);
return v_res_5437_;
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
