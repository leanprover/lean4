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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1(lean_object* v_x_426_, lean_object* v_e_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_e_427_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1___boxed(lean_object* v_x_434_, lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1(v_x_434_, v_e_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v_x_434_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_apply_1(v_x_443_, lean_box(0));
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_451_, v_x_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
else
{
lean_object* v_key_462_; lean_object* v_tail_463_; uint8_t v___x_464_; 
v_key_462_ = lean_ctor_get(v_x_460_, 0);
v_tail_463_ = lean_ctor_get(v_x_460_, 2);
v___x_464_ = l_Lean_ExprStructEq_beq(v_key_462_, v_a_459_);
if (v___x_464_ == 0)
{
v_x_460_ = v_tail_463_;
goto _start;
}
else
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec_ref(v_a_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
return v_x_470_;
}
else
{
lean_object* v_key_472_; lean_object* v_value_473_; lean_object* v_tail_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_497_; 
v_key_472_ = lean_ctor_get(v_x_471_, 0);
v_value_473_ = lean_ctor_get(v_x_471_, 1);
v_tail_474_ = lean_ctor_get(v_x_471_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_497_ == 0)
{
v___x_476_ = v_x_471_;
v_isShared_477_ = v_isSharedCheck_497_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_tail_474_);
lean_inc(v_value_473_);
lean_inc(v_key_472_);
lean_dec(v_x_471_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_497_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v_fold_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_478_ = lean_array_get_size(v_x_470_);
v___x_479_ = l_Lean_ExprStructEq_hash(v_key_472_);
v___x_480_ = 32ULL;
v___x_481_ = lean_uint64_shift_right(v___x_479_, v___x_480_);
v_fold_482_ = lean_uint64_xor(v___x_479_, v___x_481_);
v___x_483_ = 16ULL;
v___x_484_ = lean_uint64_shift_right(v_fold_482_, v___x_483_);
v___x_485_ = lean_uint64_xor(v_fold_482_, v___x_484_);
v___x_486_ = lean_uint64_to_usize(v___x_485_);
v___x_487_ = lean_usize_of_nat(v___x_478_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_sub(v___x_487_, v___x_488_);
v___x_490_ = lean_usize_land(v___x_486_, v___x_489_);
v___x_491_ = lean_array_uget_borrowed(v_x_470_, v___x_490_);
lean_inc(v___x_491_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v___x_491_);
v___x_493_ = v___x_476_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_key_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_value_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v___x_491_);
v___x_493_ = v_reuseFailAlloc_496_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; 
v___x_494_ = lean_array_uset(v_x_470_, v___x_490_, v___x_493_);
v_x_470_ = v___x_494_;
v_x_471_ = v_tail_474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_498_, lean_object* v_source_499_, lean_object* v_target_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_array_get_size(v_source_499_);
v___x_502_ = lean_nat_dec_lt(v_i_498_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v_source_499_);
lean_dec(v_i_498_);
return v_target_500_;
}
else
{
lean_object* v_es_503_; lean_object* v___x_504_; lean_object* v_source_505_; lean_object* v_target_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_es_503_ = lean_array_fget(v_source_499_, v_i_498_);
v___x_504_ = lean_box(0);
v_source_505_ = lean_array_fset(v_source_499_, v_i_498_, v___x_504_);
v_target_506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_500_, v_es_503_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_i_498_, v___x_507_);
lean_dec(v_i_498_);
v_i_498_ = v___x_508_;
v_source_499_ = v_source_505_;
v_target_500_ = v_target_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_nbuckets_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_511_ = lean_array_get_size(v_data_510_);
v___x_512_ = lean_unsigned_to_nat(2u);
v_nbuckets_513_ = lean_nat_mul(v___x_511_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_box(0);
v___x_516_ = lean_mk_array(v_nbuckets_513_, v___x_515_);
v___x_517_ = lean_array_propagate_mark(v_data_510_, v___x_516_);
v___x_518_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_514_, v_data_510_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_519_, lean_object* v_b_520_, lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
lean_dec(v_b_520_);
lean_dec_ref(v_a_519_);
return v_x_521_;
}
else
{
lean_object* v_key_522_; lean_object* v_value_523_; lean_object* v_tail_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_536_; 
v_key_522_ = lean_ctor_get(v_x_521_, 0);
v_value_523_ = lean_ctor_get(v_x_521_, 1);
v_tail_524_ = lean_ctor_get(v_x_521_, 2);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_536_ == 0)
{
v___x_526_ = v_x_521_;
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_tail_524_);
lean_inc(v_value_523_);
lean_inc(v_key_522_);
lean_dec(v_x_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v___x_528_; 
v___x_528_ = l_Lean_ExprStructEq_beq(v_key_522_, v_a_519_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_519_, v_b_520_, v_tail_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_key_522_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_value_523_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec(v_value_523_);
lean_dec(v_key_522_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_b_520_);
lean_ctor_set(v___x_526_, 0, v_a_519_);
v___x_534_ = v___x_526_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_519_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_b_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_tail_524_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_537_, lean_object* v_a_538_, lean_object* v_b_539_){
_start:
{
lean_object* v_size_540_; lean_object* v_buckets_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_584_; 
v_size_540_ = lean_ctor_get(v_m_537_, 0);
v_buckets_541_ = lean_ctor_get(v_m_537_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_537_);
if (v_isSharedCheck_584_ == 0)
{
v___x_543_ = v_m_537_;
v_isShared_544_ = v_isSharedCheck_584_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_buckets_541_);
lean_inc(v_size_540_);
lean_dec(v_m_537_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_584_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v_fold_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v_bkt_558_; uint8_t v___x_559_; 
v___x_545_ = lean_array_get_size(v_buckets_541_);
v___x_546_ = l_Lean_ExprStructEq_hash(v_a_538_);
v___x_547_ = 32ULL;
v___x_548_ = lean_uint64_shift_right(v___x_546_, v___x_547_);
v_fold_549_ = lean_uint64_xor(v___x_546_, v___x_548_);
v___x_550_ = 16ULL;
v___x_551_ = lean_uint64_shift_right(v_fold_549_, v___x_550_);
v___x_552_ = lean_uint64_xor(v_fold_549_, v___x_551_);
v___x_553_ = lean_uint64_to_usize(v___x_552_);
v___x_554_ = lean_usize_of_nat(v___x_545_);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_usize_land(v___x_553_, v___x_556_);
v_bkt_558_ = lean_array_uget_borrowed(v_buckets_541_, v___x_557_);
v___x_559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_538_, v_bkt_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v_size_x27_561_; lean_object* v___x_562_; lean_object* v_buckets_x27_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_560_ = lean_unsigned_to_nat(1u);
v_size_x27_561_ = lean_nat_add(v_size_540_, v___x_560_);
lean_dec(v_size_540_);
lean_inc(v_bkt_558_);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v_a_538_);
lean_ctor_set(v___x_562_, 1, v_b_539_);
lean_ctor_set(v___x_562_, 2, v_bkt_558_);
v_buckets_x27_563_ = lean_array_uset(v_buckets_541_, v___x_557_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(4u);
v___x_565_ = lean_nat_mul(v_size_x27_561_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(3u);
v___x_567_ = lean_nat_div(v___x_565_, v___x_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_array_get_size(v_buckets_x27_563_);
v___x_569_ = lean_nat_dec_le(v___x_567_, v___x_568_);
lean_dec(v___x_567_);
if (v___x_569_ == 0)
{
lean_object* v_val_570_; lean_object* v___x_572_; 
v_val_570_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_563_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v_val_570_);
lean_ctor_set(v___x_543_, 0, v_size_x27_561_);
v___x_572_ = v___x_543_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_size_x27_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_val_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v___x_575_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v_buckets_x27_563_);
lean_ctor_set(v___x_543_, 0, v_size_x27_561_);
v___x_575_ = v___x_543_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_size_x27_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_buckets_x27_563_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v___x_577_; lean_object* v_buckets_x27_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_inc(v_bkt_558_);
v___x_577_ = lean_box(0);
v_buckets_x27_578_ = lean_array_uset(v_buckets_541_, v___x_557_, v___x_577_);
v___x_579_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_538_, v_b_539_, v_bkt_558_);
v___x_580_ = lean_array_uset(v_buckets_x27_578_, v___x_557_, v___x_579_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_580_);
v___x_582_ = v___x_543_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_size_540_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_585_, lean_object* v_e_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_st_ref_take(v_a_585_);
v___x_590_ = lean_box(0);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_589_, v_e_586_, v_a_587_);
v___x_592_ = lean_st_ref_put(v_a_585_, v___x_591_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_593_, lean_object* v_e_594_, lean_object* v_a_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_593_, v_e_594_, v_a_595_);
lean_dec(v_a_593_);
return v_res_597_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = l_Lean_maxRecDepthErrorMessage;
v___x_604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_606_ = l_Lean_MessageData_ofFormat(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_608_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_609_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_ref_610_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___y_626_; lean_object* v_toCold_635_; lean_object* v_currRecDepth_636_; lean_object* v_ref_637_; uint16_t v_optionFlags_638_; uint8_t v_suppressElabErrors_639_; uint8_t v_checkDeprecated_640_; uint8_t v_isRecordingDeps_641_; lean_object* v_maxRecDepth_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_toCold_635_ = lean_ctor_get(v___y_622_, 0);
v_currRecDepth_636_ = lean_ctor_get(v___y_622_, 1);
v_ref_637_ = lean_ctor_get(v___y_622_, 2);
v_optionFlags_638_ = lean_ctor_get_uint16(v___y_622_, sizeof(void*)*3);
v_suppressElabErrors_639_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 2);
v_checkDeprecated_640_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 3);
v_isRecordingDeps_641_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 4);
v_maxRecDepth_647_ = lean_ctor_get(v_toCold_635_, 3);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_nat_dec_eq(v_maxRecDepth_647_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_eq(v_currRecDepth_636_, v_maxRecDepth_647_);
if (v___x_650_ == 0)
{
goto v___jp_642_;
}
else
{
lean_object* v___x_651_; 
lean_dec_ref(v_x_618_);
lean_inc(v_ref_637_);
v___x_651_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_637_);
v___y_626_ = v___x_651_;
goto v___jp_625_;
}
}
else
{
goto v___jp_642_;
}
v___jp_625_:
{
if (lean_obj_tag(v___y_626_) == 0)
{
return v___y_626_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___y_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___y_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___y_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___y_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
v___jp_642_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_currRecDepth_636_, v___x_643_);
lean_inc(v_ref_637_);
lean_inc_ref(v_toCold_635_);
v___x_645_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_645_, 0, v_toCold_635_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_ctor_set(v___x_645_, 2, v_ref_637_);
lean_ctor_set_uint16(v___x_645_, sizeof(void*)*3, v_optionFlags_638_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3 + 2, v_suppressElabErrors_639_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3 + 3, v_checkDeprecated_640_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3 + 4, v_isRecordingDeps_641_);
lean_inc(v___y_623_);
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
lean_inc(v___y_619_);
v___x_646_ = lean_apply_6(v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___x_645_, v___y_623_, lean_box(0));
v___y_626_ = v___x_646_;
goto v___jp_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_apply_1(v_x_661_, lean_box(0));
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_669_, lean_object* v_x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_669_, v_x_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_box(0);
return v___x_679_;
}
else
{
lean_object* v_key_680_; lean_object* v_value_681_; lean_object* v_tail_682_; uint8_t v___x_683_; 
v_key_680_ = lean_ctor_get(v_x_678_, 0);
v_value_681_ = lean_ctor_get(v_x_678_, 1);
v_tail_682_ = lean_ctor_get(v_x_678_, 2);
v___x_683_ = l_Lean_ExprStructEq_beq(v_key_680_, v_a_677_);
if (v___x_683_ == 0)
{
v_x_678_ = v_tail_682_;
goto _start;
}
else
{
lean_object* v___x_685_; 
lean_inc(v_value_681_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_value_681_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(v_a_686_, v_x_687_);
lean_dec(v_x_687_);
lean_dec_ref(v_a_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(lean_object* v_m_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_buckets_691_; lean_object* v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v_fold_696_; uint64_t v___x_697_; uint64_t v___x_698_; uint64_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_buckets_691_ = lean_ctor_get(v_m_689_, 1);
v___x_692_ = lean_array_get_size(v_buckets_691_);
v___x_693_ = l_Lean_ExprStructEq_hash(v_a_690_);
v___x_694_ = 32ULL;
v___x_695_ = lean_uint64_shift_right(v___x_693_, v___x_694_);
v_fold_696_ = lean_uint64_xor(v___x_693_, v___x_695_);
v___x_697_ = 16ULL;
v___x_698_ = lean_uint64_shift_right(v_fold_696_, v___x_697_);
v___x_699_ = lean_uint64_xor(v_fold_696_, v___x_698_);
v___x_700_ = lean_uint64_to_usize(v___x_699_);
v___x_701_ = lean_usize_of_nat(v___x_692_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_sub(v___x_701_, v___x_702_);
v___x_704_ = lean_usize_land(v___x_700_, v___x_703_);
v___x_705_ = lean_array_uget_borrowed(v_buckets_691_, v___x_704_);
v___x_706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(v_a_690_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(v_m_707_, v_a_708_);
lean_dec_ref(v_a_708_);
lean_dec_ref(v_m_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2(lean_object* v___x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_710_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2___boxed(lean_object* v___x_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2(v___x_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_724_, lean_object* v___y_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_725_);
v___x_732_ = lean_apply_7(v_k_724_, v_b_726_, v___y_725_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_733_, lean_object* v___y_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_733_, v___y_734_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_742_, uint8_t v_bi_743_, lean_object* v_type_744_, lean_object* v_k_745_, uint8_t v_kind_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; 
lean_inc(v___y_747_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_753_, 0, v_k_745_);
lean_closure_set(v___f_753_, 1, v___y_747_);
v___x_754_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_742_, v_bi_743_, v_type_744_, v___f_753_, v_kind_746_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_754_) == 0)
{
return v___x_754_;
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_763_, lean_object* v_bi_764_, lean_object* v_type_765_, lean_object* v_k_766_, lean_object* v_kind_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_bi_boxed_774_; uint8_t v_kind_boxed_775_; lean_object* v_res_776_; 
v_bi_boxed_774_ = lean_unbox(v_bi_764_);
v_kind_boxed_775_ = lean_unbox(v_kind_767_);
v_res_776_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_763_, v_bi_boxed_774_, v_type_765_, v_k_766_, v_kind_boxed_775_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_777_, lean_object* v_type_778_, lean_object* v_val_779_, lean_object* v_k_780_, uint8_t v_nondep_781_, uint8_t v_kind_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___f_789_; lean_object* v___x_790_; 
lean_inc(v___y_783_);
v___f_789_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_789_, 0, v_k_780_);
lean_closure_set(v___f_789_, 1, v___y_783_);
v___x_790_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_777_, v_type_778_, v_val_779_, v___f_789_, v_nondep_781_, v_kind_782_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_790_) == 0)
{
return v___x_790_;
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_799_, lean_object* v_type_800_, lean_object* v_val_801_, lean_object* v_k_802_, lean_object* v_nondep_803_, lean_object* v_kind_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v_nondep_boxed_811_; uint8_t v_kind_boxed_812_; lean_object* v_res_813_; 
v_nondep_boxed_811_ = lean_unbox(v_nondep_803_);
v_kind_boxed_812_ = lean_unbox(v_kind_804_);
v_res_813_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_799_, v_type_800_, v_val_801_, v_k_802_, v_nondep_boxed_811_, v_kind_boxed_812_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_814_, lean_object* v_pre_815_, lean_object* v_post_816_, lean_object* v_usedLetOnly_817_, lean_object* v_skipConstInApp_818_, lean_object* v_skipInstances_819_, lean_object* v_postApp_820_, lean_object* v_body_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_usedLetOnly_boxed_829_; uint8_t v_skipConstInApp_boxed_830_; uint8_t v_skipInstances_boxed_831_; lean_object* v_res_832_; 
v_usedLetOnly_boxed_829_ = lean_unbox(v_usedLetOnly_817_);
v_skipConstInApp_boxed_830_ = lean_unbox(v_skipConstInApp_818_);
v_skipInstances_boxed_831_ = lean_unbox(v_skipInstances_819_);
v_res_832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_814_, v_pre_815_, v_post_816_, v_usedLetOnly_boxed_829_, v_skipConstInApp_boxed_830_, v_skipInstances_boxed_831_, v_postApp_820_, v_body_821_, v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_836_, lean_object* v_pre_837_, lean_object* v_post_838_, uint8_t v_usedLetOnly_839_, uint8_t v_skipConstInApp_840_, uint8_t v_skipInstances_841_, lean_object* v_postApp_842_, lean_object* v_body_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_array_push(v_fvars_836_, v_x_844_);
v___x_852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_837_, v_post_838_, v_usedLetOnly_839_, v_skipConstInApp_840_, v_skipInstances_841_, v_postApp_842_, v___x_851_, v_body_843_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_853_, lean_object* v_pre_854_, lean_object* v_post_855_, lean_object* v_usedLetOnly_856_, lean_object* v_skipConstInApp_857_, lean_object* v_skipInstances_858_, lean_object* v_postApp_859_, lean_object* v_body_860_, lean_object* v_x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v_usedLetOnly_boxed_868_; uint8_t v_skipConstInApp_boxed_869_; uint8_t v_skipInstances_boxed_870_; lean_object* v_res_871_; 
v_usedLetOnly_boxed_868_ = lean_unbox(v_usedLetOnly_856_);
v_skipConstInApp_boxed_869_ = lean_unbox(v_skipConstInApp_857_);
v_skipInstances_boxed_870_ = lean_unbox(v_skipInstances_858_);
v_res_871_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_853_, v_pre_854_, v_post_855_, v_usedLetOnly_boxed_868_, v_skipConstInApp_boxed_869_, v_skipInstances_boxed_870_, v_postApp_859_, v_body_860_, v_x_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_pre_872_, lean_object* v_post_873_, uint8_t v_usedLetOnly_874_, uint8_t v_skipConstInApp_875_, uint8_t v_skipInstances_876_, lean_object* v_postApp_877_, lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
lean_inc_ref(v_post_873_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc_ref(v_e_878_);
v___x_885_ = lean_apply_6(v_post_873_, v_e_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_904_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_904_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
switch(lean_obj_tag(v_a_886_))
{
case 0:
{
lean_object* v_e_890_; lean_object* v___x_892_; 
lean_dec_ref(v_e_878_);
lean_dec_ref(v_postApp_877_);
lean_dec_ref(v_post_873_);
lean_dec_ref(v_pre_872_);
v_e_890_ = lean_ctor_get(v_a_886_, 0);
lean_inc_ref(v_e_890_);
lean_dec_ref_known(v_a_886_, 1);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_e_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_e_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
case 1:
{
lean_object* v_e_894_; lean_object* v___x_895_; 
lean_del_object(v___x_888_);
lean_dec_ref(v_e_878_);
v_e_894_ = lean_ctor_get(v_a_886_, 0);
lean_inc_ref(v_e_894_);
lean_dec_ref_known(v_a_886_, 1);
v___x_895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_872_, v_post_873_, v_usedLetOnly_874_, v_skipConstInApp_875_, v_skipInstances_876_, v_postApp_877_, v_e_894_, v_a_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v___x_895_;
}
default: 
{
lean_object* v_e_x3f_896_; 
lean_dec_ref(v_postApp_877_);
lean_dec_ref(v_post_873_);
lean_dec_ref(v_pre_872_);
v_e_x3f_896_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_e_x3f_896_);
lean_dec_ref_known(v_a_886_, 1);
if (lean_obj_tag(v_e_x3f_896_) == 0)
{
lean_object* v___x_898_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_e_878_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_e_878_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v_val_900_; lean_object* v___x_902_; 
lean_dec_ref(v_e_878_);
v_val_900_ = lean_ctor_get(v_e_x3f_896_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v_e_x3f_896_, 1);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_val_900_);
v___x_902_ = v___x_888_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_val_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v_e_878_);
lean_dec_ref(v_postApp_877_);
lean_dec_ref(v_post_873_);
lean_dec_ref(v_pre_872_);
v_a_905_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_885_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_885_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_913_, lean_object* v_post_914_, uint8_t v_usedLetOnly_915_, uint8_t v_skipConstInApp_916_, uint8_t v_skipInstances_917_, lean_object* v_postApp_918_, lean_object* v_fvars_919_, lean_object* v_e_920_, lean_object* v_a_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
if (lean_obj_tag(v_e_920_) == 6)
{
lean_object* v_binderName_927_; lean_object* v_binderType_928_; lean_object* v_body_929_; uint8_t v_binderInfo_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_binderName_927_ = lean_ctor_get(v_e_920_, 0);
lean_inc(v_binderName_927_);
v_binderType_928_ = lean_ctor_get(v_e_920_, 1);
lean_inc_ref(v_binderType_928_);
v_body_929_ = lean_ctor_get(v_e_920_, 2);
lean_inc_ref(v_body_929_);
v_binderInfo_930_ = lean_ctor_get_uint8(v_e_920_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_920_, 3);
v___x_931_ = lean_box(v_usedLetOnly_915_);
v___x_932_ = lean_box(v_skipConstInApp_916_);
v___x_933_ = lean_box(v_skipInstances_917_);
lean_inc_ref(v_postApp_918_);
lean_inc_ref(v_post_914_);
lean_inc_ref(v_pre_913_);
lean_inc_ref(v_fvars_919_);
v___f_934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_934_, 0, v_fvars_919_);
lean_closure_set(v___f_934_, 1, v_pre_913_);
lean_closure_set(v___f_934_, 2, v_post_914_);
lean_closure_set(v___f_934_, 3, v___x_931_);
lean_closure_set(v___f_934_, 4, v___x_932_);
lean_closure_set(v___f_934_, 5, v___x_933_);
lean_closure_set(v___f_934_, 6, v_postApp_918_);
lean_closure_set(v___f_934_, 7, v_body_929_);
v___x_935_ = lean_expr_instantiate_rev(v_binderType_928_, v_fvars_919_);
lean_dec_ref(v_fvars_919_);
lean_dec_ref(v_binderType_928_);
v___x_936_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v_postApp_918_, v___x_935_, v_a_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; uint8_t v___x_938_; lean_object* v___x_939_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = 0;
v___x_939_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_927_, v_binderInfo_930_, v_a_937_, v___f_934_, v___x_938_, v_a_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_939_;
}
else
{
lean_dec_ref(v___f_934_);
lean_dec(v_binderName_927_);
return v___x_936_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_expr_instantiate_rev(v_e_920_, v_fvars_919_);
lean_dec_ref(v_e_920_);
lean_inc_ref(v_postApp_918_);
lean_inc_ref(v_post_914_);
lean_inc_ref(v_pre_913_);
v___x_941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v_postApp_918_, v___x_940_, v_a_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; uint8_t v___x_943_; uint8_t v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = 0;
v___x_944_ = 1;
v___x_945_ = 1;
v___x_946_ = l_Lean_Meta_mkLambdaFVars(v_fvars_919_, v_a_942_, v___x_943_, v_usedLetOnly_915_, v___x_943_, v___x_944_, v___x_945_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec_ref(v_fvars_919_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v_postApp_918_, v_a_947_, v_a_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_948_;
}
else
{
lean_dec_ref(v_postApp_918_);
lean_dec_ref(v_post_914_);
lean_dec_ref(v_pre_913_);
return v___x_946_;
}
}
else
{
lean_dec_ref(v_fvars_919_);
lean_dec_ref(v_postApp_918_);
lean_dec_ref(v_post_914_);
lean_dec_ref(v_pre_913_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_949_, lean_object* v_pre_950_, lean_object* v_post_951_, uint8_t v_usedLetOnly_952_, uint8_t v_skipConstInApp_953_, uint8_t v_skipInstances_954_, lean_object* v_postApp_955_, lean_object* v_body_956_, lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_array_push(v_fvars_949_, v_x_957_);
v___x_965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_950_, v_post_951_, v_usedLetOnly_952_, v_skipConstInApp_953_, v_skipInstances_954_, v_postApp_955_, v___x_964_, v_body_956_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_966_, lean_object* v_pre_967_, lean_object* v_post_968_, lean_object* v_usedLetOnly_969_, lean_object* v_skipConstInApp_970_, lean_object* v_skipInstances_971_, lean_object* v_postApp_972_, lean_object* v_body_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_usedLetOnly_boxed_981_; uint8_t v_skipConstInApp_boxed_982_; uint8_t v_skipInstances_boxed_983_; lean_object* v_res_984_; 
v_usedLetOnly_boxed_981_ = lean_unbox(v_usedLetOnly_969_);
v_skipConstInApp_boxed_982_ = lean_unbox(v_skipConstInApp_970_);
v_skipInstances_boxed_983_ = lean_unbox(v_skipInstances_971_);
v_res_984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_966_, v_pre_967_, v_post_968_, v_usedLetOnly_boxed_981_, v_skipConstInApp_boxed_982_, v_skipInstances_boxed_983_, v_postApp_972_, v_body_973_, v_x_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_985_, lean_object* v_post_986_, uint8_t v_usedLetOnly_987_, uint8_t v_skipConstInApp_988_, uint8_t v_skipInstances_989_, lean_object* v_postApp_990_, lean_object* v_fvars_991_, lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_e_992_) == 8)
{
lean_object* v_declName_999_; lean_object* v_type_1000_; lean_object* v_value_1001_; lean_object* v_body_1002_; uint8_t v_nondep_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_declName_999_ = lean_ctor_get(v_e_992_, 0);
lean_inc(v_declName_999_);
v_type_1000_ = lean_ctor_get(v_e_992_, 1);
lean_inc_ref(v_type_1000_);
v_value_1001_ = lean_ctor_get(v_e_992_, 2);
lean_inc_ref(v_value_1001_);
v_body_1002_ = lean_ctor_get(v_e_992_, 3);
lean_inc_ref(v_body_1002_);
v_nondep_1003_ = lean_ctor_get_uint8(v_e_992_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_992_, 4);
v___x_1004_ = lean_box(v_usedLetOnly_987_);
v___x_1005_ = lean_box(v_skipConstInApp_988_);
v___x_1006_ = lean_box(v_skipInstances_989_);
lean_inc_ref_n(v_postApp_990_, 2);
lean_inc_ref_n(v_post_986_, 2);
lean_inc_ref_n(v_pre_985_, 2);
lean_inc_ref(v_fvars_991_);
v___f_1007_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1007_, 0, v_fvars_991_);
lean_closure_set(v___f_1007_, 1, v_pre_985_);
lean_closure_set(v___f_1007_, 2, v_post_986_);
lean_closure_set(v___f_1007_, 3, v___x_1004_);
lean_closure_set(v___f_1007_, 4, v___x_1005_);
lean_closure_set(v___f_1007_, 5, v___x_1006_);
lean_closure_set(v___f_1007_, 6, v_postApp_990_);
lean_closure_set(v___f_1007_, 7, v_body_1002_);
v___x_1008_ = lean_expr_instantiate_rev(v_type_1000_, v_fvars_991_);
lean_dec_ref(v_type_1000_);
v___x_1009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_985_, v_post_986_, v_usedLetOnly_987_, v_skipConstInApp_988_, v_skipInstances_989_, v_postApp_990_, v___x_1008_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_expr_instantiate_rev(v_value_1001_, v_fvars_991_);
lean_dec_ref(v_fvars_991_);
lean_dec_ref(v_value_1001_);
v___x_1012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_985_, v_post_986_, v_usedLetOnly_987_, v_skipConstInApp_988_, v_skipInstances_989_, v_postApp_990_, v___x_1011_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = 0;
v___x_1015_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_999_, v_a_1010_, v_a_1013_, v___f_1007_, v_nondep_1003_, v___x_1014_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1015_;
}
else
{
lean_dec(v_a_1010_);
lean_dec_ref(v___f_1007_);
lean_dec(v_declName_999_);
return v___x_1012_;
}
}
else
{
lean_dec_ref(v___f_1007_);
lean_dec_ref(v_value_1001_);
lean_dec(v_declName_999_);
lean_dec_ref(v_fvars_991_);
lean_dec_ref(v_postApp_990_);
lean_dec_ref(v_post_986_);
lean_dec_ref(v_pre_985_);
return v___x_1009_;
}
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_expr_instantiate_rev(v_e_992_, v_fvars_991_);
lean_dec_ref(v_e_992_);
lean_inc_ref(v_postApp_990_);
lean_inc_ref(v_post_986_);
lean_inc_ref(v_pre_985_);
v___x_1017_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_985_, v_post_986_, v_usedLetOnly_987_, v_skipConstInApp_988_, v_skipInstances_989_, v_postApp_990_, v___x_1016_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; uint8_t v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = 0;
v___x_1020_ = 1;
v___x_1021_ = l_Lean_Meta_mkLetFVars(v_fvars_991_, v_a_1018_, v_usedLetOnly_987_, v___x_1019_, v___x_1020_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec_ref(v_fvars_991_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_985_, v_post_986_, v_usedLetOnly_987_, v_skipConstInApp_988_, v_skipInstances_989_, v_postApp_990_, v_a_1022_, v_a_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1023_;
}
else
{
lean_dec_ref(v_postApp_990_);
lean_dec_ref(v_post_986_);
lean_dec_ref(v_pre_985_);
return v___x_1021_;
}
}
else
{
lean_dec_ref(v_fvars_991_);
lean_dec_ref(v_postApp_990_);
lean_dec_ref(v_post_986_);
lean_dec_ref(v_pre_985_);
return v___x_1017_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1024_; lean_object* v_dummy_1025_; 
v___x_1024_ = lean_box(0);
v_dummy_1025_ = l_Lean_Expr_sort___override(v___x_1024_);
return v_dummy_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_1026_, lean_object* v_post_1027_, uint8_t v_usedLetOnly_1028_, uint8_t v_skipConstInApp_1029_, uint8_t v_skipInstances_1030_, lean_object* v_postApp_1031_, size_t v_sz_1032_, size_t v_i_1033_, lean_object* v_bs_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_lt(v_i_1033_, v_sz_1032_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v_postApp_1031_);
lean_dec_ref(v_post_1027_);
lean_dec_ref(v_pre_1026_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_bs_1034_);
return v___x_1042_;
}
else
{
lean_object* v_v_1043_; lean_object* v___x_1044_; lean_object* v_bs_x27_1045_; lean_object* v___x_1046_; 
v_v_1043_ = lean_array_uget(v_bs_1034_, v_i_1033_);
v___x_1044_ = lean_unsigned_to_nat(0u);
v_bs_x27_1045_ = lean_array_uset(v_bs_1034_, v_i_1033_, v___x_1044_);
lean_inc_ref(v_postApp_1031_);
lean_inc_ref(v_post_1027_);
lean_inc_ref(v_pre_1026_);
v___x_1046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1026_, v_post_1027_, v_usedLetOnly_1028_, v_skipConstInApp_1029_, v_skipInstances_1030_, v_postApp_1031_, v_v_1043_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1033_, v___x_1048_);
v___x_1050_ = lean_array_uset(v_bs_x27_1045_, v_i_1033_, v_a_1047_);
v_i_1033_ = v___x_1049_;
v_bs_1034_ = v___x_1050_;
goto _start;
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_bs_x27_1045_);
lean_dec_ref(v_postApp_1031_);
lean_dec_ref(v_post_1027_);
lean_dec_ref(v_pre_1026_);
v_a_1052_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1046_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1046_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_pre_1060_, lean_object* v_post_1061_, uint8_t v_usedLetOnly_1062_, uint8_t v_skipConstInApp_1063_, uint8_t v_skipInstances_1064_, lean_object* v_postApp_1065_, lean_object* v___x_1066_, lean_object* v___y_1067_, lean_object* v_b_1068_, lean_object* v_a_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1060_, v_post_1061_, v_usedLetOnly_1062_, v_skipConstInApp_1063_, v_skipInstances_1064_, v_postApp_1065_, v___x_1066_, v___y_1067_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1085_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1085_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1085_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_array_fset(v_b_1068_, v_a_1069_, v_a_1076_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_b_1068_);
v_a_1086_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1075_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1075_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_pre_1094_, lean_object* v_post_1095_, lean_object* v_usedLetOnly_1096_, lean_object* v_skipConstInApp_1097_, lean_object* v_skipInstances_1098_, lean_object* v_postApp_1099_, lean_object* v___x_1100_, lean_object* v___y_1101_, lean_object* v_b_1102_, lean_object* v_a_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v_usedLetOnly_boxed_1109_; uint8_t v_skipConstInApp_boxed_1110_; uint8_t v_skipInstances_boxed_1111_; lean_object* v_res_1112_; 
v_usedLetOnly_boxed_1109_ = lean_unbox(v_usedLetOnly_1096_);
v_skipConstInApp_boxed_1110_ = lean_unbox(v_skipConstInApp_1097_);
v_skipInstances_boxed_1111_ = lean_unbox(v_skipInstances_1098_);
v_res_1112_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0(v_pre_1094_, v_post_1095_, v_usedLetOnly_boxed_1109_, v_skipConstInApp_boxed_1110_, v_skipInstances_boxed_1111_, v_postApp_1099_, v___x_1100_, v___y_1101_, v_b_1102_, v_a_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v_a_1103_);
lean_dec(v___y_1101_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_upperBound_1113_, lean_object* v___x_1114_, lean_object* v_pre_1115_, lean_object* v_post_1116_, uint8_t v_usedLetOnly_1117_, uint8_t v_skipConstInApp_1118_, uint8_t v_skipInstances_1119_, lean_object* v_postApp_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___y_1130_; uint8_t v___x_1153_; 
v___x_1153_ = lean_nat_dec_lt(v_a_1121_, v_upperBound_1113_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_dec(v_a_1121_);
lean_dec_ref(v_postApp_1120_);
lean_dec_ref(v_post_1116_);
lean_dec_ref(v_pre_1115_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_b_1122_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_array_fget_borrowed(v_b_1122_, v_a_1121_);
v___x_1156_ = lean_array_get_size(v___x_1114_);
v___x_1157_ = lean_nat_dec_lt(v_a_1121_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; 
lean_inc(v___x_1155_);
v___x_1158_ = lean_box(v_usedLetOnly_1117_);
v___x_1159_ = lean_box(v_skipConstInApp_1118_);
v___x_1160_ = lean_box(v_skipInstances_1119_);
lean_inc(v_a_1121_);
lean_inc(v___y_1123_);
lean_inc_ref(v_postApp_1120_);
lean_inc_ref(v_post_1116_);
lean_inc_ref(v_pre_1115_);
v___f_1161_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1161_, 0, v_pre_1115_);
lean_closure_set(v___f_1161_, 1, v_post_1116_);
lean_closure_set(v___f_1161_, 2, v___x_1158_);
lean_closure_set(v___f_1161_, 3, v___x_1159_);
lean_closure_set(v___f_1161_, 4, v___x_1160_);
lean_closure_set(v___f_1161_, 5, v_postApp_1120_);
lean_closure_set(v___f_1161_, 6, v___x_1155_);
lean_closure_set(v___f_1161_, 7, v___y_1123_);
lean_closure_set(v___f_1161_, 8, v_b_1122_);
lean_closure_set(v___f_1161_, 9, v_a_1121_);
v___y_1130_ = v___f_1161_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1162_; uint8_t v_isInstance_1163_; 
v___x_1162_ = lean_array_fget_borrowed(v___x_1114_, v_a_1121_);
v_isInstance_1163_ = lean_ctor_get_uint8(v___x_1162_, sizeof(void*)*1 + 4);
if (v_isInstance_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; 
lean_inc(v___x_1155_);
v___x_1164_ = lean_box(v_usedLetOnly_1117_);
v___x_1165_ = lean_box(v_skipConstInApp_1118_);
v___x_1166_ = lean_box(v_skipInstances_1119_);
lean_inc(v_a_1121_);
lean_inc(v___y_1123_);
lean_inc_ref(v_postApp_1120_);
lean_inc_ref(v_post_1116_);
lean_inc_ref(v_pre_1115_);
v___f_1167_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1167_, 0, v_pre_1115_);
lean_closure_set(v___f_1167_, 1, v_post_1116_);
lean_closure_set(v___f_1167_, 2, v___x_1164_);
lean_closure_set(v___f_1167_, 3, v___x_1165_);
lean_closure_set(v___f_1167_, 4, v___x_1166_);
lean_closure_set(v___f_1167_, 5, v_postApp_1120_);
lean_closure_set(v___f_1167_, 6, v___x_1155_);
lean_closure_set(v___f_1167_, 7, v___y_1123_);
lean_closure_set(v___f_1167_, 8, v_b_1122_);
lean_closure_set(v___f_1167_, 9, v_a_1121_);
v___y_1130_ = v___f_1167_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1168_; lean_object* v___f_1169_; 
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_b_1122_);
v___f_1169_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1169_, 0, v___x_1168_);
v___y_1130_ = v___f_1169_;
goto v___jp_1129_;
}
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; 
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v___y_1125_);
lean_inc_ref(v___y_1124_);
v___x_1131_ = lean_apply_5(v___y_1130_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, lean_box(0));
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
if (lean_obj_tag(v_a_1132_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; 
lean_dec(v_a_1121_);
lean_dec_ref(v_postApp_1120_);
lean_dec_ref(v_post_1116_);
lean_dec_ref(v_pre_1115_);
v_a_1136_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v_a_1132_, 1);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v_a_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_del_object(v___x_1134_);
v_a_1140_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v_a_1132_, 1);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_a_1121_, v___x_1141_);
lean_dec(v_a_1121_);
v_a_1121_ = v___x_1142_;
v_b_1122_ = v_a_1140_;
goto _start;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_a_1121_);
lean_dec_ref(v_postApp_1120_);
lean_dec_ref(v_post_1116_);
lean_dec_ref(v_pre_1115_);
v_a_1145_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1131_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1131_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1170_, lean_object* v_pre_1171_, lean_object* v_post_1172_, uint8_t v_usedLetOnly_1173_, uint8_t v_skipConstInApp_1174_, lean_object* v_postApp_1175_, lean_object* v___y_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_f_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; 
if (lean_obj_tag(v_x_1177_) == 5)
{
lean_object* v_fn_1239_; lean_object* v_arg_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_fn_1239_ = lean_ctor_get(v_x_1177_, 0);
lean_inc_ref(v_fn_1239_);
v_arg_1240_ = lean_ctor_get(v_x_1177_, 1);
lean_inc_ref(v_arg_1240_);
lean_dec_ref_known(v_x_1177_, 2);
v___x_1241_ = lean_array_set(v_x_1178_, v_x_1179_, v_arg_1240_);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_sub(v_x_1179_, v___x_1242_);
lean_dec(v_x_1179_);
v_x_1177_ = v_fn_1239_;
v_x_1178_ = v___x_1241_;
v_x_1179_ = v___x_1243_;
goto _start;
}
else
{
lean_dec(v_x_1179_);
if (v_skipConstInApp_1174_ == 0)
{
goto v___jp_1236_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Lean_Expr_isConst(v_x_1177_);
if (v___x_1245_ == 0)
{
goto v___jp_1236_;
}
else
{
v_f_1187_ = v_x_1177_;
v___y_1188_ = v___y_1180_;
v___y_1189_ = v___y_1181_;
v___y_1190_ = v___y_1182_;
v___y_1191_ = v___y_1183_;
v___y_1192_ = v___y_1184_;
goto v___jp_1186_;
}
}
}
v___jp_1186_:
{
if (v_skipInstances_1170_ == 0)
{
size_t v_sz_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v_sz_1193_ = lean_array_size(v_x_1178_);
v___x_1194_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1175_);
lean_inc_ref(v_post_1172_);
lean_inc_ref(v_pre_1171_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1171_, v_post_1172_, v_usedLetOnly_1173_, v_skipConstInApp_1174_, v_skipInstances_1170_, v_postApp_1175_, v_sz_1193_, v___x_1194_, v_x_1178_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = l_Lean_mkAppN(v_f_1187_, v_a_1196_);
lean_dec(v_a_1196_);
lean_inc_ref(v_postApp_1175_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
v___x_1198_ = lean_apply_7(v_postApp_1175_, v___y_1176_, v___x_1197_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1171_, v_post_1172_, v_usedLetOnly_1173_, v_skipConstInApp_1174_, v_skipInstances_1170_, v_postApp_1175_, v_a_1199_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1200_;
}
else
{
lean_dec_ref(v_postApp_1175_);
lean_dec_ref(v_post_1172_);
lean_dec_ref(v_pre_1171_);
return v___x_1198_;
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_f_1187_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_postApp_1175_);
lean_dec_ref(v_post_1172_);
lean_dec_ref(v_pre_1171_);
v_a_1201_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1195_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1195_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_array_get_size(v_x_1178_);
lean_inc_ref(v_f_1187_);
v___x_1210_ = l_Lean_Meta_getFunInfoNArgs(v_f_1187_, v___x_1209_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v_paramInfo_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v_paramInfo_1212_ = lean_ctor_get(v_a_1211_, 0);
lean_inc_ref(v_paramInfo_1212_);
lean_dec(v_a_1211_);
v___x_1213_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1175_);
lean_inc_ref(v_post_1172_);
lean_inc_ref(v_pre_1171_);
v___x_1214_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v___x_1209_, v_paramInfo_1212_, v_pre_1171_, v_post_1172_, v_usedLetOnly_1173_, v_skipConstInApp_1174_, v_skipInstances_1170_, v_postApp_1175_, v___x_1213_, v_x_1178_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec_ref(v_paramInfo_1212_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Lean_mkAppN(v_f_1187_, v_a_1215_);
lean_dec(v_a_1215_);
lean_inc_ref(v_postApp_1175_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
v___x_1217_ = lean_apply_7(v_postApp_1175_, v___y_1176_, v___x_1216_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, lean_box(0));
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1171_, v_post_1172_, v_usedLetOnly_1173_, v_skipConstInApp_1174_, v_skipInstances_1170_, v_postApp_1175_, v_a_1218_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1219_;
}
else
{
lean_dec_ref(v_postApp_1175_);
lean_dec_ref(v_post_1172_);
lean_dec_ref(v_pre_1171_);
return v___x_1217_;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_f_1187_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_postApp_1175_);
lean_dec_ref(v_post_1172_);
lean_dec_ref(v_pre_1171_);
v_a_1220_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1214_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1214_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_f_1187_);
lean_dec_ref(v_x_1178_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_postApp_1175_);
lean_dec_ref(v_post_1172_);
lean_dec_ref(v_pre_1171_);
v_a_1228_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1210_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1210_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
v___jp_1236_:
{
lean_object* v___x_1237_; 
lean_inc_ref(v_postApp_1175_);
lean_inc_ref(v_post_1172_);
lean_inc_ref(v_pre_1171_);
v___x_1237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1171_, v_post_1172_, v_usedLetOnly_1173_, v_skipConstInApp_1174_, v_skipInstances_1170_, v_postApp_1175_, v_x_1177_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v_f_1187_ = v_a_1238_;
v___y_1188_ = v___y_1180_;
v___y_1189_ = v___y_1181_;
v___y_1190_ = v___y_1182_;
v___y_1191_ = v___y_1183_;
v___y_1192_ = v___y_1184_;
goto v___jp_1186_;
}
else
{
lean_dec_ref(v_x_1178_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_postApp_1175_);
lean_dec_ref(v_post_1172_);
lean_dec_ref(v_pre_1171_);
return v___x_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1246_, lean_object* v_pre_1247_, lean_object* v_e_1248_, lean_object* v_post_1249_, uint8_t v_usedLetOnly_1250_, uint8_t v_skipConstInApp_1251_, uint8_t v_skipInstances_1252_, lean_object* v_postApp_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Core_checkSystem(v___x_1246_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1260_, 1);
lean_inc_ref(v_pre_1247_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1255_);
lean_inc_ref(v_e_1248_);
v___x_1261_ = lean_apply_6(v_pre_1247_, v_e_1248_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, lean_box(0));
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1310_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1310_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1310_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___y_1267_; 
switch(lean_obj_tag(v_a_1262_))
{
case 0:
{
lean_object* v_e_1302_; lean_object* v___x_1304_; 
lean_dec_ref(v_postApp_1253_);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_pre_1247_);
v_e_1302_ = lean_ctor_get(v_a_1262_, 0);
lean_inc_ref(v_e_1302_);
lean_dec_ref_known(v_a_1262_, 1);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_e_1302_);
v___x_1304_ = v___x_1264_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_e_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
case 1:
{
lean_object* v_e_1306_; lean_object* v___x_1307_; 
lean_del_object(v___x_1264_);
lean_dec_ref(v_e_1248_);
v_e_1306_ = lean_ctor_get(v_a_1262_, 0);
lean_inc_ref(v_e_1306_);
lean_dec_ref_known(v_a_1262_, 1);
v___x_1307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v_e_1306_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1307_;
}
default: 
{
lean_object* v_e_x3f_1308_; 
lean_del_object(v___x_1264_);
v_e_x3f_1308_ = lean_ctor_get(v_a_1262_, 0);
lean_inc(v_e_x3f_1308_);
lean_dec_ref_known(v_a_1262_, 1);
if (lean_obj_tag(v_e_x3f_1308_) == 0)
{
v___y_1267_ = v_e_1248_;
goto v___jp_1266_;
}
else
{
lean_object* v_val_1309_; 
lean_dec_ref(v_e_1248_);
v_val_1309_ = lean_ctor_get(v_e_x3f_1308_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v_e_x3f_1308_, 1);
v___y_1267_ = v_val_1309_;
goto v___jp_1266_;
}
}
}
v___jp_1266_:
{
switch(lean_obj_tag(v___y_1267_))
{
case 7:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___x_1268_, v___y_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1269_;
}
case 6:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___x_1270_, v___y_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1271_;
}
case 8:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1273_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___x_1272_, v___y_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1273_;
}
case 5:
{
lean_object* v_dummy_1274_; lean_object* v_nargs_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_dummy_1274_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1275_ = l_Lean_Expr_getAppNumArgs(v___y_1267_);
lean_inc(v_nargs_1275_);
v___x_1276_ = lean_mk_array(v_nargs_1275_, v_dummy_1274_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_sub(v_nargs_1275_, v___x_1277_);
lean_dec(v_nargs_1275_);
lean_inc_ref(v___y_1267_);
v___x_1279_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1252_, v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_postApp_1253_, v___y_1267_, v___y_1267_, v___x_1276_, v___x_1278_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1279_;
}
case 10:
{
lean_object* v_data_1280_; lean_object* v_expr_1281_; lean_object* v___x_1282_; 
v_data_1280_ = lean_ctor_get(v___y_1267_, 0);
v_expr_1281_ = lean_ctor_get(v___y_1267_, 1);
lean_inc_ref(v_expr_1281_);
lean_inc_ref(v_postApp_1253_);
lean_inc_ref(v_post_1249_);
lean_inc_ref(v_pre_1247_);
v___x_1282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v_expr_1281_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; size_t v___x_1284_; size_t v___x_1285_; uint8_t v___x_1286_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = lean_ptr_addr(v_expr_1281_);
v___x_1285_ = lean_ptr_addr(v_a_1283_);
v___x_1286_ = lean_usize_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_inc(v_data_1280_);
lean_dec_ref_known(v___y_1267_, 2);
v___x_1287_ = l_Lean_Expr_mdata___override(v_data_1280_, v_a_1283_);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___x_1287_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; 
lean_dec(v_a_1283_);
v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___y_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1289_;
}
}
else
{
lean_dec_ref_known(v___y_1267_, 2);
lean_dec_ref(v_postApp_1253_);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_pre_1247_);
return v___x_1282_;
}
}
case 11:
{
lean_object* v_typeName_1290_; lean_object* v_idx_1291_; lean_object* v_struct_1292_; lean_object* v___x_1293_; 
v_typeName_1290_ = lean_ctor_get(v___y_1267_, 0);
v_idx_1291_ = lean_ctor_get(v___y_1267_, 1);
v_struct_1292_ = lean_ctor_get(v___y_1267_, 2);
lean_inc_ref(v_struct_1292_);
lean_inc_ref(v_postApp_1253_);
lean_inc_ref(v_post_1249_);
lean_inc_ref(v_pre_1247_);
v___x_1293_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v_struct_1292_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; size_t v___x_1295_; size_t v___x_1296_; uint8_t v___x_1297_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = lean_ptr_addr(v_struct_1292_);
v___x_1296_ = lean_ptr_addr(v_a_1294_);
v___x_1297_ = lean_usize_dec_eq(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_inc(v_idx_1291_);
lean_inc(v_typeName_1290_);
lean_dec_ref_known(v___y_1267_, 3);
v___x_1298_ = l_Lean_Expr_proj___override(v_typeName_1290_, v_idx_1291_, v_a_1294_);
v___x_1299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___x_1298_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; 
lean_dec(v_a_1294_);
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___y_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1300_;
}
}
else
{
lean_dec_ref_known(v___y_1267_, 3);
lean_dec_ref(v_postApp_1253_);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_pre_1247_);
return v___x_1293_;
}
}
default: 
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_postApp_1253_, v___y_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_postApp_1253_);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_pre_1247_);
v_a_1311_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1261_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1261_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_postApp_1253_);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_pre_1247_);
v_a_1319_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1260_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1260_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1327_, lean_object* v_pre_1328_, lean_object* v_e_1329_, lean_object* v_post_1330_, lean_object* v_usedLetOnly_1331_, lean_object* v_skipConstInApp_1332_, lean_object* v_skipInstances_1333_, lean_object* v_postApp_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_usedLetOnly_boxed_1341_; uint8_t v_skipConstInApp_boxed_1342_; uint8_t v_skipInstances_boxed_1343_; lean_object* v_res_1344_; 
v_usedLetOnly_boxed_1341_ = lean_unbox(v_usedLetOnly_1331_);
v_skipConstInApp_boxed_1342_ = lean_unbox(v_skipConstInApp_1332_);
v_skipInstances_boxed_1343_ = lean_unbox(v_skipInstances_1333_);
v_res_1344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1327_, v_pre_1328_, v_e_1329_, v_post_1330_, v_usedLetOnly_boxed_1341_, v_skipConstInApp_boxed_1342_, v_skipInstances_boxed_1343_, v_postApp_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1345_, lean_object* v_post_1346_, uint8_t v_usedLetOnly_1347_, uint8_t v_skipConstInApp_1348_, uint8_t v_skipInstances_1349_, lean_object* v_postApp_1350_, lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_inc(v_a_1352_);
v___x_1358_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1358_, 0, lean_box(0));
lean_closure_set(v___x_1358_, 1, lean_box(0));
lean_closure_set(v___x_1358_, 2, v_a_1352_);
v___x_1359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1358_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1394_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1394_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1394_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(v_a_1360_, v_e_1351_);
lean_dec(v_a_1360_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; 
lean_del_object(v___x_1362_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1366_ = lean_box(v_usedLetOnly_1347_);
v___x_1367_ = lean_box(v_skipConstInApp_1348_);
v___x_1368_ = lean_box(v_skipInstances_1349_);
lean_inc_ref(v_e_1351_);
v___f_1369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1369_, 0, v___x_1365_);
lean_closure_set(v___f_1369_, 1, v_pre_1345_);
lean_closure_set(v___f_1369_, 2, v_e_1351_);
lean_closure_set(v___f_1369_, 3, v_post_1346_);
lean_closure_set(v___f_1369_, 4, v___x_1366_);
lean_closure_set(v___f_1369_, 5, v___x_1367_);
lean_closure_set(v___f_1369_, 6, v___x_1368_);
lean_closure_set(v___f_1369_, 7, v_postApp_1350_);
v___x_1370_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1369_, v_a_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_n(v_a_1371_, 2);
lean_dec_ref_known(v___x_1370_, 1);
lean_inc(v_a_1352_);
v___f_1372_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1372_, 0, v_a_1352_);
lean_closure_set(v___f_1372_, 1, v_e_1351_);
lean_closure_set(v___f_1372_, 2, v_a_1371_);
v___x_1373_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1372_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1381_);
v___x_1375_ = v___x_1373_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1373_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_a_1371_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1371_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1371_);
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1373_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1373_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_dec_ref(v_e_1351_);
return v___x_1370_;
}
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1392_; 
lean_dec_ref(v_e_1351_);
lean_dec_ref(v_postApp_1350_);
lean_dec_ref(v_post_1346_);
lean_dec_ref(v_pre_1345_);
v_val_1390_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1364_, 1);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_val_1390_);
v___x_1392_ = v___x_1362_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec_ref(v_e_1351_);
lean_dec_ref(v_postApp_1350_);
lean_dec_ref(v_post_1346_);
lean_dec_ref(v_pre_1345_);
v_a_1395_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1359_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1359_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1403_, lean_object* v_post_1404_, uint8_t v_usedLetOnly_1405_, uint8_t v_skipConstInApp_1406_, uint8_t v_skipInstances_1407_, lean_object* v_postApp_1408_, lean_object* v_fvars_1409_, lean_object* v_e_1410_, lean_object* v_a_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
if (lean_obj_tag(v_e_1410_) == 7)
{
lean_object* v_binderName_1417_; lean_object* v_binderType_1418_; lean_object* v_body_1419_; uint8_t v_binderInfo_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_binderName_1417_ = lean_ctor_get(v_e_1410_, 0);
lean_inc(v_binderName_1417_);
v_binderType_1418_ = lean_ctor_get(v_e_1410_, 1);
lean_inc_ref(v_binderType_1418_);
v_body_1419_ = lean_ctor_get(v_e_1410_, 2);
lean_inc_ref(v_body_1419_);
v_binderInfo_1420_ = lean_ctor_get_uint8(v_e_1410_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1410_, 3);
v___x_1421_ = lean_box(v_usedLetOnly_1405_);
v___x_1422_ = lean_box(v_skipConstInApp_1406_);
v___x_1423_ = lean_box(v_skipInstances_1407_);
lean_inc_ref(v_postApp_1408_);
lean_inc_ref(v_post_1404_);
lean_inc_ref(v_pre_1403_);
lean_inc_ref(v_fvars_1409_);
v___f_1424_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1424_, 0, v_fvars_1409_);
lean_closure_set(v___f_1424_, 1, v_pre_1403_);
lean_closure_set(v___f_1424_, 2, v_post_1404_);
lean_closure_set(v___f_1424_, 3, v___x_1421_);
lean_closure_set(v___f_1424_, 4, v___x_1422_);
lean_closure_set(v___f_1424_, 5, v___x_1423_);
lean_closure_set(v___f_1424_, 6, v_postApp_1408_);
lean_closure_set(v___f_1424_, 7, v_body_1419_);
v___x_1425_ = lean_expr_instantiate_rev(v_binderType_1418_, v_fvars_1409_);
lean_dec_ref(v_fvars_1409_);
lean_dec_ref(v_binderType_1418_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1403_, v_post_1404_, v_usedLetOnly_1405_, v_skipConstInApp_1406_, v_skipInstances_1407_, v_postApp_1408_, v___x_1425_, v_a_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = 0;
v___x_1429_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1417_, v_binderInfo_1420_, v_a_1427_, v___f_1424_, v___x_1428_, v_a_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1429_;
}
else
{
lean_dec_ref(v___f_1424_);
lean_dec(v_binderName_1417_);
return v___x_1426_;
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_expr_instantiate_rev(v_e_1410_, v_fvars_1409_);
lean_dec_ref(v_e_1410_);
lean_inc_ref(v_postApp_1408_);
lean_inc_ref(v_post_1404_);
lean_inc_ref(v_pre_1403_);
v___x_1431_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1403_, v_post_1404_, v_usedLetOnly_1405_, v_skipConstInApp_1406_, v_skipInstances_1407_, v_postApp_1408_, v___x_1430_, v_a_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = 0;
v___x_1434_ = 1;
v___x_1435_ = 1;
v___x_1436_ = l_Lean_Meta_mkForallFVars(v_fvars_1409_, v_a_1432_, v___x_1433_, v_usedLetOnly_1405_, v___x_1434_, v___x_1435_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec_ref(v_fvars_1409_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1403_, v_post_1404_, v_usedLetOnly_1405_, v_skipConstInApp_1406_, v_skipInstances_1407_, v_postApp_1408_, v_a_1437_, v_a_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1438_;
}
else
{
lean_dec_ref(v_postApp_1408_);
lean_dec_ref(v_post_1404_);
lean_dec_ref(v_pre_1403_);
return v___x_1436_;
}
}
else
{
lean_dec_ref(v_fvars_1409_);
lean_dec_ref(v_postApp_1408_);
lean_dec_ref(v_post_1404_);
lean_dec_ref(v_pre_1403_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1439_, lean_object* v_pre_1440_, lean_object* v_post_1441_, uint8_t v_usedLetOnly_1442_, uint8_t v_skipConstInApp_1443_, uint8_t v_skipInstances_1444_, lean_object* v_postApp_1445_, lean_object* v_body_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_array_push(v_fvars_1439_, v_x_1447_);
v___x_1455_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1440_, v_post_1441_, v_usedLetOnly_1442_, v_skipConstInApp_1443_, v_skipInstances_1444_, v_postApp_1445_, v___x_1454_, v_body_1446_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_1456_, lean_object* v_post_1457_, lean_object* v_usedLetOnly_1458_, lean_object* v_skipConstInApp_1459_, lean_object* v_skipInstances_1460_, lean_object* v_postApp_1461_, lean_object* v_e_1462_, lean_object* v_a_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_usedLetOnly_boxed_1469_; uint8_t v_skipConstInApp_boxed_1470_; uint8_t v_skipInstances_boxed_1471_; lean_object* v_res_1472_; 
v_usedLetOnly_boxed_1469_ = lean_unbox(v_usedLetOnly_1458_);
v_skipConstInApp_boxed_1470_ = lean_unbox(v_skipConstInApp_1459_);
v_skipInstances_boxed_1471_ = lean_unbox(v_skipInstances_1460_);
v_res_1472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1456_, v_post_1457_, v_usedLetOnly_boxed_1469_, v_skipConstInApp_boxed_1470_, v_skipInstances_boxed_1471_, v_postApp_1461_, v_e_1462_, v_a_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_a_1463_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1473_, lean_object* v_post_1474_, lean_object* v_usedLetOnly_1475_, lean_object* v_skipConstInApp_1476_, lean_object* v_skipInstances_1477_, lean_object* v_postApp_1478_, lean_object* v_sz_1479_, lean_object* v_i_1480_, lean_object* v_bs_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_usedLetOnly_boxed_1488_; uint8_t v_skipConstInApp_boxed_1489_; uint8_t v_skipInstances_boxed_1490_; size_t v_sz_boxed_1491_; size_t v_i_boxed_1492_; lean_object* v_res_1493_; 
v_usedLetOnly_boxed_1488_ = lean_unbox(v_usedLetOnly_1475_);
v_skipConstInApp_boxed_1489_ = lean_unbox(v_skipConstInApp_1476_);
v_skipInstances_boxed_1490_ = lean_unbox(v_skipInstances_1477_);
v_sz_boxed_1491_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_i_boxed_1492_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_res_1493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1473_, v_post_1474_, v_usedLetOnly_boxed_1488_, v_skipConstInApp_boxed_1489_, v_skipInstances_boxed_1490_, v_postApp_1478_, v_sz_boxed_1491_, v_i_boxed_1492_, v_bs_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1494_, lean_object* v_post_1495_, lean_object* v_usedLetOnly_1496_, lean_object* v_skipConstInApp_1497_, lean_object* v_skipInstances_1498_, lean_object* v_postApp_1499_, lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v_usedLetOnly_boxed_1507_; uint8_t v_skipConstInApp_boxed_1508_; uint8_t v_skipInstances_boxed_1509_; lean_object* v_res_1510_; 
v_usedLetOnly_boxed_1507_ = lean_unbox(v_usedLetOnly_1496_);
v_skipConstInApp_boxed_1508_ = lean_unbox(v_skipConstInApp_1497_);
v_skipInstances_boxed_1509_ = lean_unbox(v_skipInstances_1498_);
v_res_1510_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1494_, v_post_1495_, v_usedLetOnly_boxed_1507_, v_skipConstInApp_boxed_1508_, v_skipInstances_boxed_1509_, v_postApp_1499_, v_e_1500_, v_a_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v_a_1501_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1511_, lean_object* v_post_1512_, lean_object* v_usedLetOnly_1513_, lean_object* v_skipConstInApp_1514_, lean_object* v_skipInstances_1515_, lean_object* v_postApp_1516_, lean_object* v_fvars_1517_, lean_object* v_e_1518_, lean_object* v_a_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v_usedLetOnly_boxed_1525_; uint8_t v_skipConstInApp_boxed_1526_; uint8_t v_skipInstances_boxed_1527_; lean_object* v_res_1528_; 
v_usedLetOnly_boxed_1525_ = lean_unbox(v_usedLetOnly_1513_);
v_skipConstInApp_boxed_1526_ = lean_unbox(v_skipConstInApp_1514_);
v_skipInstances_boxed_1527_ = lean_unbox(v_skipInstances_1515_);
v_res_1528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1511_, v_post_1512_, v_usedLetOnly_boxed_1525_, v_skipConstInApp_boxed_1526_, v_skipInstances_boxed_1527_, v_postApp_1516_, v_fvars_1517_, v_e_1518_, v_a_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v_a_1519_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1529_, lean_object* v_post_1530_, lean_object* v_usedLetOnly_1531_, lean_object* v_skipConstInApp_1532_, lean_object* v_skipInstances_1533_, lean_object* v_postApp_1534_, lean_object* v_fvars_1535_, lean_object* v_e_1536_, lean_object* v_a_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v_usedLetOnly_boxed_1543_; uint8_t v_skipConstInApp_boxed_1544_; uint8_t v_skipInstances_boxed_1545_; lean_object* v_res_1546_; 
v_usedLetOnly_boxed_1543_ = lean_unbox(v_usedLetOnly_1531_);
v_skipConstInApp_boxed_1544_ = lean_unbox(v_skipConstInApp_1532_);
v_skipInstances_boxed_1545_ = lean_unbox(v_skipInstances_1533_);
v_res_1546_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1529_, v_post_1530_, v_usedLetOnly_boxed_1543_, v_skipConstInApp_boxed_1544_, v_skipInstances_boxed_1545_, v_postApp_1534_, v_fvars_1535_, v_e_1536_, v_a_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v_a_1537_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1547_, lean_object* v_post_1548_, lean_object* v_usedLetOnly_1549_, lean_object* v_skipConstInApp_1550_, lean_object* v_skipInstances_1551_, lean_object* v_postApp_1552_, lean_object* v_fvars_1553_, lean_object* v_e_1554_, lean_object* v_a_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v_usedLetOnly_boxed_1561_; uint8_t v_skipConstInApp_boxed_1562_; uint8_t v_skipInstances_boxed_1563_; lean_object* v_res_1564_; 
v_usedLetOnly_boxed_1561_ = lean_unbox(v_usedLetOnly_1549_);
v_skipConstInApp_boxed_1562_ = lean_unbox(v_skipConstInApp_1550_);
v_skipInstances_boxed_1563_ = lean_unbox(v_skipInstances_1551_);
v_res_1564_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1547_, v_post_1548_, v_usedLetOnly_boxed_1561_, v_skipConstInApp_boxed_1562_, v_skipInstances_boxed_1563_, v_postApp_1552_, v_fvars_1553_, v_e_1554_, v_a_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v_a_1555_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_upperBound_1565_, lean_object* v___x_1566_, lean_object* v_pre_1567_, lean_object* v_post_1568_, lean_object* v_usedLetOnly_1569_, lean_object* v_skipConstInApp_1570_, lean_object* v_skipInstances_1571_, lean_object* v_postApp_1572_, lean_object* v_a_1573_, lean_object* v_b_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_usedLetOnly_boxed_1581_; uint8_t v_skipConstInApp_boxed_1582_; uint8_t v_skipInstances_boxed_1583_; lean_object* v_res_1584_; 
v_usedLetOnly_boxed_1581_ = lean_unbox(v_usedLetOnly_1569_);
v_skipConstInApp_boxed_1582_ = lean_unbox(v_skipConstInApp_1570_);
v_skipInstances_boxed_1583_ = lean_unbox(v_skipInstances_1571_);
v_res_1584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_upperBound_1565_, v___x_1566_, v_pre_1567_, v_post_1568_, v_usedLetOnly_boxed_1581_, v_skipConstInApp_boxed_1582_, v_skipInstances_boxed_1583_, v_postApp_1572_, v_a_1573_, v_b_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___x_1566_);
lean_dec(v_upperBound_1565_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1585_, lean_object* v_pre_1586_, lean_object* v_post_1587_, lean_object* v_usedLetOnly_1588_, lean_object* v_skipConstInApp_1589_, lean_object* v_postApp_1590_, lean_object* v___y_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_skipInstances_boxed_1601_; uint8_t v_usedLetOnly_boxed_1602_; uint8_t v_skipConstInApp_boxed_1603_; lean_object* v_res_1604_; 
v_skipInstances_boxed_1601_ = lean_unbox(v_skipInstances_1585_);
v_usedLetOnly_boxed_1602_ = lean_unbox(v_usedLetOnly_1588_);
v_skipConstInApp_boxed_1603_ = lean_unbox(v_skipConstInApp_1589_);
v_res_1604_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1601_, v_pre_1586_, v_post_1587_, v_usedLetOnly_boxed_1602_, v_skipConstInApp_boxed_1603_, v_postApp_1590_, v___y_1591_, v_x_1592_, v_x_1593_, v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
return v_res_1604_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_unsigned_to_nat(16u);
v___x_1608_ = lean_mk_array(v___x_1607_, v___x_1606_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v___x_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1613_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1613_, 0, lean_box(0));
lean_closure_set(v___x_1613_, 1, lean_box(0));
lean_closure_set(v___x_1613_, 2, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1614_, lean_object* v_pre_1615_, lean_object* v_post_1616_, uint8_t v_usedLetOnly_1617_, uint8_t v_skipConstInApp_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___f_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_a_1628_; lean_object* v___x_1629_; 
v___f_1624_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0));
v___x_1625_ = 0;
v___x_1626_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3);
v___x_1627_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1626_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1615_, v_post_1616_, v_usedLetOnly_1617_, v_skipConstInApp_1618_, v___x_1625_, v___f_1624_, v_input_1614_, v_a_1628_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1631_, 0, lean_box(0));
lean_closure_set(v___x_1631_, 1, lean_box(0));
lean_closure_set(v___x_1631_, 2, v_a_1628_);
v___x_1632_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1631_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v___x_1632_, 0);
lean_dec(v_unused_1640_);
v___x_1634_ = v___x_1632_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v___x_1632_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_a_1630_);
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1630_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_dec(v_a_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1641_, lean_object* v_pre_1642_, lean_object* v_post_1643_, lean_object* v_usedLetOnly_1644_, lean_object* v_skipConstInApp_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
uint8_t v_usedLetOnly_boxed_1651_; uint8_t v_skipConstInApp_boxed_1652_; lean_object* v_res_1653_; 
v_usedLetOnly_boxed_1651_ = lean_unbox(v_usedLetOnly_1644_);
v_skipConstInApp_boxed_1652_ = lean_unbox(v_skipConstInApp_1645_);
v_res_1653_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1641_, v_pre_1642_, v_post_1643_, v_usedLetOnly_boxed_1651_, v_skipConstInApp_boxed_1652_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1675_; 
v___f_1662_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1663_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1656_, v_a_1660_);
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1675_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1675_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_unbox(v_a_1664_);
lean_dec(v_a_1664_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1670_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v_e_1656_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_e_1656_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
else
{
uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_del_object(v___x_1666_);
v___x_1672_ = 0;
v___x_1673_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1674_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1656_, v___x_1673_, v___f_1662_, v___x_1672_, v___x_1672_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1683_, lean_object* v_m_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(v_m_1684_, v_a_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1687_, lean_object* v_m_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_00_u03b2_1687_, v_m_1688_, v_a_1689_);
lean_dec_ref(v_a_1689_);
lean_dec_ref(v_m_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_upperBound_1691_, lean_object* v___x_1692_, lean_object* v_pre_1693_, lean_object* v_post_1694_, uint8_t v_usedLetOnly_1695_, uint8_t v_skipConstInApp_1696_, uint8_t v_skipInstances_1697_, lean_object* v_postApp_1698_, lean_object* v___x_1699_, lean_object* v_inst_1700_, lean_object* v_R_1701_, lean_object* v_a_1702_, lean_object* v_b_1703_, lean_object* v_c_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_upperBound_1691_, v___x_1692_, v_pre_1693_, v_post_1694_, v_usedLetOnly_1695_, v_skipConstInApp_1696_, v_skipInstances_1697_, v_postApp_1698_, v_a_1702_, v_b_1703_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1712_ = _args[0];
lean_object* v___x_1713_ = _args[1];
lean_object* v_pre_1714_ = _args[2];
lean_object* v_post_1715_ = _args[3];
lean_object* v_usedLetOnly_1716_ = _args[4];
lean_object* v_skipConstInApp_1717_ = _args[5];
lean_object* v_skipInstances_1718_ = _args[6];
lean_object* v_postApp_1719_ = _args[7];
lean_object* v___x_1720_ = _args[8];
lean_object* v_inst_1721_ = _args[9];
lean_object* v_R_1722_ = _args[10];
lean_object* v_a_1723_ = _args[11];
lean_object* v_b_1724_ = _args[12];
lean_object* v_c_1725_ = _args[13];
lean_object* v___y_1726_ = _args[14];
lean_object* v___y_1727_ = _args[15];
lean_object* v___y_1728_ = _args[16];
lean_object* v___y_1729_ = _args[17];
lean_object* v___y_1730_ = _args[18];
lean_object* v___y_1731_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_1732_; uint8_t v_skipConstInApp_boxed_1733_; uint8_t v_skipInstances_boxed_1734_; lean_object* v_res_1735_; 
v_usedLetOnly_boxed_1732_ = lean_unbox(v_usedLetOnly_1716_);
v_skipConstInApp_boxed_1733_ = lean_unbox(v_skipConstInApp_1717_);
v_skipInstances_boxed_1734_ = lean_unbox(v_skipInstances_1718_);
v_res_1735_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_upperBound_1712_, v___x_1713_, v_pre_1714_, v_post_1715_, v_usedLetOnly_boxed_1732_, v_skipConstInApp_boxed_1733_, v_skipInstances_boxed_1734_, v_postApp_1719_, v___x_1720_, v_inst_1721_, v_R_1722_, v_a_1723_, v_b_1724_, v_c_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec(v___x_1720_);
lean_dec_ref(v___x_1713_);
lean_dec(v_upperBound_1712_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1736_, lean_object* v_name_1737_, uint8_t v_bi_1738_, lean_object* v_type_1739_, lean_object* v_k_1740_, uint8_t v_kind_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1737_, v_bi_1738_, v_type_1739_, v_k_1740_, v_kind_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_name_1750_, lean_object* v_bi_1751_, lean_object* v_type_1752_, lean_object* v_k_1753_, lean_object* v_kind_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v_bi_boxed_1761_; uint8_t v_kind_boxed_1762_; lean_object* v_res_1763_; 
v_bi_boxed_1761_ = lean_unbox(v_bi_1751_);
v_kind_boxed_1762_ = lean_unbox(v_kind_1754_);
v_res_1763_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1749_, v_name_1750_, v_bi_boxed_1761_, v_type_1752_, v_k_1753_, v_kind_boxed_1762_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1764_, lean_object* v_name_1765_, lean_object* v_type_1766_, lean_object* v_val_1767_, lean_object* v_k_1768_, uint8_t v_nondep_1769_, uint8_t v_kind_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1765_, v_type_1766_, v_val_1767_, v_k_1768_, v_nondep_1769_, v_kind_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_name_1779_, lean_object* v_type_1780_, lean_object* v_val_1781_, lean_object* v_k_1782_, lean_object* v_nondep_1783_, lean_object* v_kind_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v_nondep_boxed_1791_; uint8_t v_kind_boxed_1792_; lean_object* v_res_1793_; 
v_nondep_boxed_1791_ = lean_unbox(v_nondep_1783_);
v_kind_boxed_1792_ = lean_unbox(v_kind_1784_);
v_res_1793_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1778_, v_name_1779_, v_type_1780_, v_val_1781_, v_k_1782_, v_nondep_boxed_1791_, v_kind_boxed_1792_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1794_, lean_object* v_ref_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1795_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_ref_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1802_, v_ref_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1819_, v_x_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1828_, lean_object* v_m_1829_, lean_object* v_a_1830_, lean_object* v_b_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1829_, v_a_1830_, v_b_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1833_, lean_object* v_a_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1837_, lean_object* v_a_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1837_, v_a_1838_, v_x_1839_);
lean_dec(v_x_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1841_, lean_object* v_a_1842_, lean_object* v_x_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1845_, lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
uint8_t v_res_1848_; lean_object* v_r_1849_; 
v_res_1848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1845_, v_a_1846_, v_x_1847_);
lean_dec(v_x_1847_);
lean_dec_ref(v_a_1846_);
v_r_1849_ = lean_box(v_res_1848_);
return v_r_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1850_, lean_object* v_data_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1853_, lean_object* v_a_1854_, lean_object* v_b_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1854_, v_b_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1858_, lean_object* v_i_1859_, lean_object* v_source_1860_, lean_object* v_target_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1859_, v_source_1860_, v_target_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1864_, v_x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v_x_1875_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v_env_1889_; uint8_t v___x_1890_; lean_object* v_env_1891_; lean_object* v___x_1892_; lean_object* v_toCold_1893_; lean_object* v_mctx_1894_; lean_object* v_lctx_1895_; lean_object* v_options_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1888_ = lean_st_ref_get(v___y_1886_);
v_env_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc_ref(v_env_1889_);
lean_dec(v___x_1888_);
v___x_1890_ = 0;
v_env_1891_ = l_Lean_Environment_setRecordingDeps(v_env_1889_, v___x_1890_);
v___x_1892_ = lean_st_ref_get(v___y_1884_);
v_toCold_1893_ = lean_ctor_get(v___y_1885_, 0);
v_mctx_1894_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_ref(v_mctx_1894_);
lean_dec(v___x_1892_);
v_lctx_1895_ = lean_ctor_get(v___y_1883_, 2);
v_options_1896_ = lean_ctor_get(v_toCold_1893_, 2);
lean_inc_ref(v_options_1896_);
lean_inc_ref(v_lctx_1895_);
v___x_1897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1897_, 0, v_env_1891_);
lean_ctor_set(v___x_1897_, 1, v_mctx_1894_);
lean_ctor_set(v___x_1897_, 2, v_lctx_1895_);
lean_ctor_set(v___x_1897_, 3, v_options_1896_);
v___x_1898_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v_msgData_1882_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1906_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1907_; double v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_float_of_nat(v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_ref_1919_; lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1966_; 
v_ref_1919_ = lean_ctor_get(v___y_1916_, 2);
v___x_1920_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1966_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1966_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v_traceState_1926_; lean_object* v_env_1927_; lean_object* v_nextMacroScope_1928_; lean_object* v_ngen_1929_; lean_object* v_auxDeclNGen_1930_; lean_object* v_cache_1931_; lean_object* v_recordedDeps_1932_; lean_object* v_messages_1933_; lean_object* v_infoState_1934_; lean_object* v_snapshotTasks_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1965_; 
v___x_1925_ = lean_st_ref_take(v___y_1917_);
v_traceState_1926_ = lean_ctor_get(v___x_1925_, 4);
v_env_1927_ = lean_ctor_get(v___x_1925_, 0);
v_nextMacroScope_1928_ = lean_ctor_get(v___x_1925_, 1);
v_ngen_1929_ = lean_ctor_get(v___x_1925_, 2);
v_auxDeclNGen_1930_ = lean_ctor_get(v___x_1925_, 3);
v_cache_1931_ = lean_ctor_get(v___x_1925_, 5);
v_recordedDeps_1932_ = lean_ctor_get(v___x_1925_, 6);
v_messages_1933_ = lean_ctor_get(v___x_1925_, 7);
v_infoState_1934_ = lean_ctor_get(v___x_1925_, 8);
v_snapshotTasks_1935_ = lean_ctor_get(v___x_1925_, 9);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1937_ = v___x_1925_;
v_isShared_1938_ = v_isSharedCheck_1965_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_snapshotTasks_1935_);
lean_inc(v_infoState_1934_);
lean_inc(v_messages_1933_);
lean_inc(v_recordedDeps_1932_);
lean_inc(v_cache_1931_);
lean_inc(v_traceState_1926_);
lean_inc(v_auxDeclNGen_1930_);
lean_inc(v_ngen_1929_);
lean_inc(v_nextMacroScope_1928_);
lean_inc(v_env_1927_);
lean_dec(v___x_1925_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1965_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
uint64_t v_tid_1939_; lean_object* v_traces_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1964_; 
v_tid_1939_ = lean_ctor_get_uint64(v_traceState_1926_, sizeof(void*)*1);
v_traces_1940_ = lean_ctor_get(v_traceState_1926_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_traceState_1926_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1942_ = v_traceState_1926_;
v_isShared_1943_ = v_isSharedCheck_1964_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_traces_1940_);
lean_dec(v_traceState_1926_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1964_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; double v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1947_ = 0;
v___x_1948_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1949_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1949_, 0, v_cls_1912_);
lean_ctor_set(v___x_1949_, 1, v___x_1945_);
lean_ctor_set(v___x_1949_, 2, v___x_1948_);
lean_ctor_set_float(v___x_1949_, sizeof(void*)*3, v___x_1946_);
lean_ctor_set_float(v___x_1949_, sizeof(void*)*3 + 8, v___x_1946_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*3 + 16, v___x_1947_);
v___x_1950_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1951_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v_a_1921_);
lean_ctor_set(v___x_1951_, 2, v___x_1950_);
lean_inc(v_ref_1919_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_ref_1919_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = l_Lean_PersistentArray_push___redArg(v_traces_1940_, v___x_1952_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1953_);
v___x_1955_ = v___x_1942_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1953_);
lean_ctor_set_uint64(v_reuseFailAlloc_1963_, sizeof(void*)*1, v_tid_1939_);
v___x_1955_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 4, v___x_1955_);
v___x_1957_ = v___x_1937_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_env_1927_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_nextMacroScope_1928_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_ngen_1929_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_auxDeclNGen_1930_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1962_, 5, v_cache_1931_);
lean_ctor_set(v_reuseFailAlloc_1962_, 6, v_recordedDeps_1932_);
lean_ctor_set(v_reuseFailAlloc_1962_, 7, v_messages_1933_);
lean_ctor_set(v_reuseFailAlloc_1962_, 8, v_infoState_1934_);
lean_ctor_set(v_reuseFailAlloc_1962_, 9, v_snapshotTasks_1935_);
v___x_1957_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_st_ref_put(v___y_1917_, v___x_1957_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1944_);
v___x_1960_ = v___x_1923_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1944_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1967_, lean_object* v_msg_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1967_, v_msg_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1979_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__1));
v___x_1980_ = l_Lean_Name_append(v___x_1979_, v___x_1978_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__3));
v___x_1983_ = l_Lean_stringToMessageData(v___x_1982_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__5));
v___x_1986_ = l_Lean_stringToMessageData(v___x_1985_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__7));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__9));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_e_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___y_2000_; 
if (lean_obj_tag(v_e_1993_) == 11)
{
lean_object* v_typeName_2024_; lean_object* v_idx_2025_; lean_object* v_struct_2026_; lean_object* v___x_2027_; lean_object* v_env_2028_; lean_object* v___x_2029_; 
v_typeName_2024_ = lean_ctor_get(v_e_1993_, 0);
v_idx_2025_ = lean_ctor_get(v_e_1993_, 1);
v_struct_2026_ = lean_ctor_get(v_e_1993_, 2);
v___x_2027_ = lean_st_ref_get(v___y_1997_);
v_env_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc_ref(v_env_2028_);
lean_dec(v___x_2027_);
lean_inc(v_typeName_2024_);
v___x_2029_ = l_Lean_getStructureInfo_x3f(v_env_2028_, v_typeName_2024_);
if (lean_obj_tag(v___x_2029_) == 1)
{
lean_object* v_val_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2084_; 
v_val_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2084_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_val_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2084_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_fieldNames_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_fieldNames_2034_ = lean_ctor_get(v_val_2030_, 1);
lean_inc_ref(v_fieldNames_2034_);
lean_dec(v_val_2030_);
v___x_2035_ = lean_array_get_size(v_fieldNames_2034_);
v___x_2036_ = lean_nat_dec_lt(v_idx_2025_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v_toCold_2037_; lean_object* v_options_2038_; uint8_t v_hasTrace_2039_; 
lean_dec_ref(v_fieldNames_2034_);
v_toCold_2037_ = lean_ctor_get(v___y_1996_, 0);
v_options_2038_ = lean_ctor_get(v_toCold_2037_, 2);
v_hasTrace_2039_ = lean_ctor_get_uint8(v_options_2038_, sizeof(void*)*1);
if (v_hasTrace_2039_ == 0)
{
lean_del_object(v___x_2032_);
goto v___jp_2021_;
}
else
{
lean_object* v_inheritedTraceOptions_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_inheritedTraceOptions_2040_ = lean_ctor_get(v_toCold_2037_, 11);
v___x_2041_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2042_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2043_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2040_, v_options_2038_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_del_object(v___x_2032_);
goto v___jp_2021_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4);
lean_inc(v_idx_2025_);
v___x_2045_ = l_Nat_reprFast(v_idx_2025_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 3);
lean_ctor_set(v___x_2032_, 0, v___x_2045_);
v___x_2047_ = v___x_2032_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2048_ = l_Lean_MessageData_ofFormat(v___x_2047_);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2044_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
lean_inc_ref(v_e_1993_);
v___x_2052_ = l_Lean_indentExpr(v_e_1993_);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2041_, v___x_2053_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
goto v___jp_2021_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref_known(v_e_1993_, 3);
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2064_; uint8_t v_transparency_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; uint8_t v___x_2068_; 
lean_inc_ref(v_struct_2026_);
lean_inc(v_idx_2025_);
lean_del_object(v___x_2032_);
lean_dec_ref_known(v_e_1993_, 3);
v___x_2064_ = l_Lean_Meta_Context_config(v___y_1994_);
v_transparency_2065_ = lean_ctor_get_uint8(v___x_2064_, 9);
lean_dec_ref(v___x_2064_);
v___x_2066_ = lean_array_fget(v_fieldNames_2034_, v_idx_2025_);
lean_dec(v_idx_2025_);
lean_dec_ref(v_fieldNames_2034_);
v___x_2067_ = 1;
v___x_2068_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2065_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v_keyedConfig_2069_; uint8_t v_trackZetaDelta_2070_; lean_object* v_zetaDeltaSet_2071_; lean_object* v_lctx_2072_; lean_object* v_localInstances_2073_; lean_object* v_defEqCtx_x3f_2074_; lean_object* v_synthPendingDepth_2075_; lean_object* v_customCanUnfoldPredicate_x3f_2076_; uint8_t v_univApprox_2077_; uint8_t v_inTypeClassResolution_2078_; uint8_t v_cacheInferType_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_keyedConfig_2069_ = lean_ctor_get(v___y_1994_, 0);
v_trackZetaDelta_2070_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7);
v_zetaDeltaSet_2071_ = lean_ctor_get(v___y_1994_, 1);
v_lctx_2072_ = lean_ctor_get(v___y_1994_, 2);
v_localInstances_2073_ = lean_ctor_get(v___y_1994_, 3);
v_defEqCtx_x3f_2074_ = lean_ctor_get(v___y_1994_, 4);
v_synthPendingDepth_2075_ = lean_ctor_get(v___y_1994_, 5);
v_customCanUnfoldPredicate_x3f_2076_ = lean_ctor_get(v___y_1994_, 6);
v_univApprox_2077_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2078_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7 + 2);
v_cacheInferType_2079_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2069_);
v___x_2080_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2067_, v_keyedConfig_2069_);
lean_inc(v_customCanUnfoldPredicate_x3f_2076_);
lean_inc(v_synthPendingDepth_2075_);
lean_inc(v_defEqCtx_x3f_2074_);
lean_inc_ref(v_localInstances_2073_);
lean_inc_ref(v_lctx_2072_);
lean_inc(v_zetaDeltaSet_2071_);
v___x_2081_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v_zetaDeltaSet_2071_);
lean_ctor_set(v___x_2081_, 2, v_lctx_2072_);
lean_ctor_set(v___x_2081_, 3, v_localInstances_2073_);
lean_ctor_set(v___x_2081_, 4, v_defEqCtx_x3f_2074_);
lean_ctor_set(v___x_2081_, 5, v_synthPendingDepth_2075_);
lean_ctor_set(v___x_2081_, 6, v_customCanUnfoldPredicate_x3f_2076_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*7, v_trackZetaDelta_2070_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*7 + 1, v_univApprox_2077_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2078_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*7 + 3, v_cacheInferType_2079_);
v___x_2082_ = l_Lean_Meta_mkProjection(v_struct_2026_, v___x_2066_, v___x_2081_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec_ref_known(v___x_2081_, 7);
v___y_2000_ = v___x_2082_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Meta_mkProjection(v_struct_2026_, v___x_2066_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
v___y_2000_ = v___x_2083_;
goto v___jp_1999_;
}
}
}
}
else
{
lean_object* v_toCold_2085_; lean_object* v_options_2086_; uint8_t v_hasTrace_2087_; 
lean_dec(v___x_2029_);
v_toCold_2085_ = lean_ctor_get(v___y_1996_, 0);
v_options_2086_ = lean_ctor_get(v_toCold_2085_, 2);
v_hasTrace_2087_ = lean_ctor_get_uint8(v_options_2086_, sizeof(void*)*1);
if (v_hasTrace_2087_ == 0)
{
goto v___jp_2018_;
}
else
{
lean_object* v_inheritedTraceOptions_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_inheritedTraceOptions_2088_ = lean_ctor_get(v_toCold_2085_, 11);
v___x_2089_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2090_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2088_, v_options_2086_, v___x_2090_);
if (v___x_2091_ == 0)
{
goto v___jp_2018_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2092_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8);
lean_inc(v_typeName_2024_);
v___x_2093_ = l_Lean_MessageData_ofName(v_typeName_2024_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_inc_ref(v_e_1993_);
v___x_2097_ = l_Lean_indentExpr(v_e_1993_);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2089_, v___x_2098_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_dec_ref_known(v___x_2099_, 1);
goto v___jp_2018_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref_known(v_e_1993_, 3);
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_e_1993_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
return v___x_2109_;
}
v___jp_1999_:
{
if (lean_obj_tag(v___y_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_a_2001_ = lean_ctor_get(v___y_2000_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___y_2000_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v___y_2000_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___y_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_a_2001_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v___y_2000_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___y_2000_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___y_2000_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___y_2000_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
v___jp_2018_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_e_1993_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
v___jp_2021_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_e_1993_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_e_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___f_2126_; lean_object* v___x_2127_; 
v___f_2126_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2127_ = lean_find_expr(v___f_2126_, v_e_2120_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v_e_2120_);
return v___x_2128_;
}
else
{
lean_object* v___f_2129_; lean_object* v_post_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref_known(v___x_2127_, 1);
v___f_2129_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v_post_2130_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2131_ = 0;
v___x_2132_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2120_, v___f_2129_, v_post_2130_, v___x_2131_, v___x_2131_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Meta_Sym_foldProjs(v_e_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_box(0);
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2151_ = l_Lean_mkConst(v___x_2150_, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2159_ = l_Lean_mkConst(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_box(0);
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2166_ = l_Lean_mkConst(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = l_Lean_mkNatLit(v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_box(0);
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2176_ = l_Lean_mkConst(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2180_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2179_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
v_a_2182_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2180_, 2);
v___x_2183_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2184_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2183_, v_a_2177_, v_a_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v_a_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
v_a_2186_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2184_, 2);
v___x_2187_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2188_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2187_, v_a_2177_, v_a_2186_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v_a_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
v_a_2190_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2188_, 2);
v___x_2191_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2192_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2191_, v_a_2177_, v_a_2190_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
v_a_2194_ = lean_ctor_get(v___x_2192_, 1);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2192_, 2);
v___x_2195_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2196_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2195_, v_a_2177_, v_a_2194_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v_a_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
v_a_2198_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2196_, 2);
v___x_2199_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2200_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2199_, v_a_2177_, v_a_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
v_a_2202_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2200_, 2);
v___x_2203_ = l_Lean_Int_mkType;
v___x_2204_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2203_, v_a_2177_, v_a_2202_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_a_2206_ = lean_ctor_get(v___x_2204_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v___x_2204_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2185_);
lean_ctor_set(v___x_2210_, 1, v_a_2181_);
lean_ctor_set(v___x_2210_, 2, v_a_2197_);
lean_ctor_set(v___x_2210_, 3, v_a_2193_);
lean_ctor_set(v___x_2210_, 4, v_a_2189_);
lean_ctor_set(v___x_2210_, 5, v_a_2201_);
lean_ctor_set(v___x_2210_, 6, v_a_2205_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_a_2206_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2201_);
lean_dec(v_a_2197_);
lean_dec(v_a_2193_);
lean_dec(v_a_2189_);
lean_dec(v_a_2185_);
lean_dec(v_a_2181_);
v_a_2215_ = lean_ctor_get(v___x_2204_, 0);
v_a_2216_ = lean_ctor_get(v___x_2204_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2204_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_inc(v_a_2215_);
lean_dec(v___x_2204_);
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
lean_dec(v_a_2197_);
lean_dec(v_a_2193_);
lean_dec(v_a_2189_);
lean_dec(v_a_2185_);
lean_dec(v_a_2181_);
v_a_2224_ = lean_ctor_get(v___x_2200_, 0);
v_a_2225_ = lean_ctor_get(v___x_2200_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2200_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_inc(v_a_2224_);
lean_dec(v___x_2200_);
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
lean_dec(v_a_2193_);
lean_dec(v_a_2189_);
lean_dec(v_a_2185_);
lean_dec(v_a_2181_);
v_a_2233_ = lean_ctor_get(v___x_2196_, 0);
v_a_2234_ = lean_ctor_get(v___x_2196_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2196_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_inc(v_a_2233_);
lean_dec(v___x_2196_);
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
lean_dec(v_a_2189_);
lean_dec(v_a_2185_);
lean_dec(v_a_2181_);
v_a_2242_ = lean_ctor_get(v___x_2192_, 0);
v_a_2243_ = lean_ctor_get(v___x_2192_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2192_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_inc(v_a_2242_);
lean_dec(v___x_2192_);
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
else
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_a_2185_);
lean_dec(v_a_2181_);
v_a_2251_ = lean_ctor_get(v___x_2188_, 0);
v_a_2252_ = lean_ctor_get(v___x_2188_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2188_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_dec(v___x_2188_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2251_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_a_2181_);
v_a_2260_ = lean_ctor_get(v___x_2184_, 0);
v_a_2261_ = lean_ctor_get(v___x_2184_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2184_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_inc(v_a_2260_);
lean_dec(v___x_2184_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2260_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2269_ = lean_ctor_get(v___x_2180_, 0);
v_a_2270_ = lean_ctor_get(v___x_2180_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2180_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_inc(v_a_2269_);
lean_dec(v___x_2180_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2269_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2278_, v_a_2279_);
lean_dec_ref(v_a_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2281_, lean_object* v_opt_2282_){
_start:
{
lean_object* v_name_2283_; lean_object* v_defValue_2284_; lean_object* v_map_2285_; lean_object* v___x_2286_; 
v_name_2283_ = lean_ctor_get(v_opt_2282_, 0);
v_defValue_2284_ = lean_ctor_get(v_opt_2282_, 1);
v_map_2285_ = lean_ctor_get(v_opts_2281_, 0);
v___x_2286_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2285_, v_name_2283_);
if (lean_obj_tag(v___x_2286_) == 0)
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_unbox(v_defValue_2284_);
return v___x_2287_;
}
else
{
lean_object* v_val_2288_; 
v_val_2288_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_val_2288_);
lean_dec_ref_known(v___x_2286_, 1);
if (lean_obj_tag(v_val_2288_) == 1)
{
uint8_t v_v_2289_; 
v_v_2289_ = lean_ctor_get_uint8(v_val_2288_, 0);
lean_dec_ref_known(v_val_2288_, 0);
return v_v_2289_;
}
else
{
uint8_t v___x_2290_; 
lean_dec(v_val_2288_);
v___x_2290_ = lean_unbox(v_defValue_2284_);
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2291_, lean_object* v_opt_2292_){
_start:
{
uint8_t v_res_2293_; lean_object* v_r_2294_; 
v_res_2293_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2291_, v_opt_2292_);
lean_dec_ref(v_opt_2292_);
lean_dec_ref(v_opts_2291_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg(){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object* v___dummy_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v_res_2301_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___f_2312_; lean_object* v___x_2208__overap_2313_; lean_object* v___x_2314_; 
v___f_2312_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2208__overap_2313_ = lean_panic_fn_borrowed(v___f_2312_, v_msg_2306_);
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
v___x_2314_ = lean_apply_5(v___x_2208__overap_2313_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, lean_box(0));
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2321_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2329_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2330_ = lean_unsigned_to_nat(19u);
v___x_2331_ = lean_unsigned_to_nat(309u);
v___x_2332_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__3));
v___x_2333_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_2334_ = l_mkPanicMessageWithDecl(v___x_2333_, v___x_2332_, v___x_2331_, v___x_2330_, v___x_2329_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_fst_2342_; lean_object* v_snd_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___x_2383_; lean_object* v_env_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2383_ = lean_st_ref_get(v_a_2339_);
v_env_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc_ref(v_env_2384_);
lean_dec(v___x_2383_);
v___x_2385_ = 0;
v___x_2386_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2386_, 0, v_env_2384_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1, v___x_2385_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1 + 1, v___x_2385_);
v___x_2387_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2388_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2386_, v___x_2387_);
lean_dec_ref_known(v___x_2386_, 1);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v_a_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
v_a_2390_ = lean_ctor_get(v___x_2388_, 1);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2388_, 2);
v_fst_2342_ = v_a_2389_;
v_snd_2343_ = v_a_2390_;
v___y_2344_ = v_a_2336_;
v___y_2345_ = v_a_2337_;
v___y_2346_ = v_a_2338_;
v___y_2347_ = v_a_2339_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v___x_2388_, 2);
v___x_2391_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__5, &l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5);
v___x_2392_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2391_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v_fst_2394_; lean_object* v_snd_2395_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v_fst_2394_ = lean_ctor_get(v_a_2393_, 0);
lean_inc(v_fst_2394_);
v_snd_2395_ = lean_ctor_get(v_a_2393_, 1);
lean_inc(v_snd_2395_);
lean_dec(v_a_2393_);
v_fst_2342_ = v_fst_2394_;
v_snd_2343_ = v_snd_2395_;
v___y_2344_ = v_a_2336_;
v___y_2345_ = v_a_2337_;
v___y_2346_ = v_a_2338_;
v___y_2347_ = v_a_2339_;
goto v___jp_2341_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec_ref(v_x_2335_);
v_a_2396_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2392_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2392_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
v___jp_2341_:
{
lean_object* v_ref_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; 
v_ref_2348_ = lean_ctor_get(v___y_2346_, 2);
v___x_2349_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2346_);
v___x_2350_ = l_Lean_Meta_Sym_sym_debug;
v___x_2351_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v___x_2349_, v___x_2350_);
lean_dec_ref(v___x_2349_);
v___x_2352_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_fst_2342_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2359_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v___x_2359_, 0, v_snd_2343_);
lean_ctor_set(v___x_2359_, 1, v___x_2356_);
lean_ctor_set(v___x_2359_, 2, v___x_2356_);
lean_ctor_set(v___x_2359_, 3, v___x_2356_);
lean_ctor_set(v___x_2359_, 4, v___x_2356_);
lean_ctor_set(v___x_2359_, 5, v___x_2356_);
lean_ctor_set(v___x_2359_, 6, v___x_2356_);
lean_ctor_set(v___x_2359_, 7, v___x_2356_);
lean_ctor_set(v___x_2359_, 8, v___x_2356_);
lean_ctor_set(v___x_2359_, 9, v_a_2353_);
lean_ctor_set(v___x_2359_, 10, v___x_2357_);
lean_ctor_set(v___x_2359_, 11, v___x_2358_);
lean_ctor_set(v___x_2359_, 12, v___x_2356_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*13, v___x_2351_);
v___x_2360_ = lean_st_mk_ref(v___x_2359_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___x_2360_);
v___x_2361_ = lean_apply_7(v_x_2335_, v___x_2355_, v___x_2360_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, lean_box(0));
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_st_ref_get(v___x_2360_);
lean_dec(v___x_2360_);
lean_dec(v___x_2366_);
if (v_isShared_2365_ == 0)
{
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2362_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_dec(v___x_2360_);
return v___x_2361_;
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v_snd_2343_);
lean_dec_ref(v_fst_2342_);
lean_dec_ref(v_x_2335_);
v_a_2371_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2373_ = v___x_2352_;
v_isShared_2374_ = v_isSharedCheck_2382_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2352_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2382_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2375_ = lean_io_error_to_string(v_a_2371_);
v___x_2376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = l_Lean_MessageData_ofFormat(v___x_2376_);
lean_inc(v_ref_2348_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_ref_2348_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2378_);
v___x_2380_ = v___x_2373_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2411_, lean_object* v_x_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2419_, lean_object* v_x_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2419_, v_x_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2427_){
_start:
{
lean_object* v_sharedExprs_2429_; lean_object* v___x_2430_; 
v_sharedExprs_2429_ = lean_ctor_get(v_a_2427_, 0);
lean_inc_ref(v_sharedExprs_2429_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_sharedExprs_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2431_);
lean_dec_ref(v_a_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2434_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
v___x_2452_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2450_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_trueExpr_2457_; lean_object* v___x_2459_; 
v_trueExpr_2457_ = lean_ctor_get(v_a_2453_, 0);
lean_inc_ref(v_trueExpr_2457_);
lean_dec(v_a_2453_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_trueExpr_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_trueExpr_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2462_);
lean_dec_ref(v_a_2462_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2465_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2482_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2496_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2496_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2496_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
size_t v___x_2489_; size_t v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2489_ = lean_ptr_addr(v_e_2481_);
v___x_2490_ = lean_ptr_addr(v_a_2485_);
lean_dec(v_a_2485_);
v___x_2491_ = lean_usize_dec_eq(v___x_2489_, v___x_2490_);
v___x_2492_ = lean_box(v___x_2491_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2492_);
v___x_2494_ = v___x_2487_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
v_a_2497_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2484_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2484_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2505_, v_a_2506_);
lean_dec_ref(v_a_2506_);
lean_dec_ref(v_e_2505_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2509_, v_a_2510_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec_ref(v_e_2518_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2538_; 
v___x_2529_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2527_);
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_falseExpr_2534_; lean_object* v___x_2536_; 
v_falseExpr_2534_ = lean_ctor_get(v_a_2530_, 1);
lean_inc_ref(v_falseExpr_2534_);
lean_dec(v_a_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_falseExpr_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_falseExpr_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2539_);
lean_dec_ref(v_a_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2542_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2559_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2573_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2573_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2573_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
size_t v___x_2566_; size_t v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2566_ = lean_ptr_addr(v_e_2558_);
v___x_2567_ = lean_ptr_addr(v_a_2562_);
lean_dec(v_a_2562_);
v___x_2568_ = lean_usize_dec_eq(v___x_2566_, v___x_2567_);
v___x_2569_ = lean_box(v___x_2568_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2569_);
v___x_2571_ = v___x_2564_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2561_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2561_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2582_, v_a_2583_);
lean_dec_ref(v_a_2583_);
lean_dec_ref(v_e_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2586_, v_a_2587_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec_ref(v_e_2595_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2615_; 
v___x_2606_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2604_);
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_btrueExpr_2611_; lean_object* v___x_2613_; 
v_btrueExpr_2611_ = lean_ctor_get(v_a_2607_, 3);
lean_inc_ref(v_btrueExpr_2611_);
lean_dec(v_a_2607_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_btrueExpr_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_btrueExpr_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2616_);
lean_dec_ref(v_a_2616_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2619_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2636_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2650_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2650_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2650_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
size_t v___x_2643_; size_t v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2643_ = lean_ptr_addr(v_e_2635_);
v___x_2644_ = lean_ptr_addr(v_a_2639_);
lean_dec(v_a_2639_);
v___x_2645_ = lean_usize_dec_eq(v___x_2643_, v___x_2644_);
v___x_2646_ = lean_box(v___x_2645_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2646_);
v___x_2648_ = v___x_2641_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_a_2651_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2638_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2638_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2659_, v_a_2660_);
lean_dec_ref(v_a_2660_);
lean_dec_ref(v_e_2659_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2663_, v_a_2664_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec_ref(v_e_2672_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2692_; 
v___x_2683_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2681_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2692_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2692_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_bfalseExpr_2688_; lean_object* v___x_2690_; 
v_bfalseExpr_2688_ = lean_ctor_get(v_a_2684_, 4);
lean_inc_ref(v_bfalseExpr_2688_);
lean_dec(v_a_2684_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v_bfalseExpr_2688_);
v___x_2690_ = v___x_2686_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_bfalseExpr_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2693_);
lean_dec_ref(v_a_2693_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2696_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2727_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
size_t v___x_2720_; size_t v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2720_ = lean_ptr_addr(v_e_2712_);
v___x_2721_ = lean_ptr_addr(v_a_2716_);
lean_dec(v_a_2716_);
v___x_2722_ = lean_usize_dec_eq(v___x_2720_, v___x_2721_);
v___x_2723_ = lean_box(v___x_2722_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2723_);
v___x_2725_ = v___x_2718_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_a_2728_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2715_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2715_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2736_, v_a_2737_);
lean_dec_ref(v_a_2737_);
lean_dec_ref(v_e_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2740_, v_a_2741_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec_ref(v_e_2749_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2769_; 
v___x_2760_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2758_);
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2769_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2769_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v_natZExpr_2765_; lean_object* v___x_2767_; 
v_natZExpr_2765_ = lean_ctor_get(v_a_2761_, 2);
lean_inc_ref(v_natZExpr_2765_);
lean_dec(v_a_2761_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_natZExpr_2765_);
v___x_2767_ = v___x_2763_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_natZExpr_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2770_);
lean_dec_ref(v_a_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2773_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2791_; lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2800_; 
v___x_2791_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2789_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v_ordEqExpr_2796_; lean_object* v___x_2798_; 
v_ordEqExpr_2796_ = lean_ctor_get(v_a_2792_, 5);
lean_inc_ref(v_ordEqExpr_2796_);
lean_dec(v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_ordEqExpr_2796_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_ordEqExpr_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2801_);
lean_dec_ref(v_a_2801_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2804_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2831_; 
v___x_2822_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2820_);
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v_intExpr_2827_; lean_object* v___x_2829_; 
v_intExpr_2827_ = lean_ctor_get(v_a_2823_, 6);
lean_inc_ref(v_intExpr_2827_);
lean_dec(v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_intExpr_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_intExpr_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2832_);
lean_dec_ref(v_a_2832_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2835_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Meta_Sym_getIntExpr(v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2851_, lean_object* v_ctx_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v_share_2856_; lean_object* v_maxFVar_2857_; lean_object* v_proofInstInfo_2858_; lean_object* v_proofInstInfoFVar_2859_; lean_object* v_letValue_2860_; lean_object* v_inferType_2861_; lean_object* v_getLevel_2862_; lean_object* v_congrInfo_2863_; lean_object* v_defEqI_2864_; lean_object* v_extensions_2865_; lean_object* v_issues_2866_; lean_object* v_canon_2867_; lean_object* v_instanceOverrides_2868_; uint8_t v_debug_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2933_; 
v___x_2855_ = lean_st_ref_take(v_a_2853_);
v_share_2856_ = lean_ctor_get(v___x_2855_, 0);
v_maxFVar_2857_ = lean_ctor_get(v___x_2855_, 1);
v_proofInstInfo_2858_ = lean_ctor_get(v___x_2855_, 2);
v_proofInstInfoFVar_2859_ = lean_ctor_get(v___x_2855_, 3);
v_letValue_2860_ = lean_ctor_get(v___x_2855_, 4);
v_inferType_2861_ = lean_ctor_get(v___x_2855_, 5);
v_getLevel_2862_ = lean_ctor_get(v___x_2855_, 6);
v_congrInfo_2863_ = lean_ctor_get(v___x_2855_, 7);
v_defEqI_2864_ = lean_ctor_get(v___x_2855_, 8);
v_extensions_2865_ = lean_ctor_get(v___x_2855_, 9);
v_issues_2866_ = lean_ctor_get(v___x_2855_, 10);
v_canon_2867_ = lean_ctor_get(v___x_2855_, 11);
v_instanceOverrides_2868_ = lean_ctor_get(v___x_2855_, 12);
v_debug_2869_ = lean_ctor_get_uint8(v___x_2855_, sizeof(void*)*13);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2871_ = v___x_2855_;
v_isShared_2872_ = v_isSharedCheck_2933_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_instanceOverrides_2868_);
lean_inc(v_canon_2867_);
lean_inc(v_issues_2866_);
lean_inc(v_extensions_2865_);
lean_inc(v_defEqI_2864_);
lean_inc(v_congrInfo_2863_);
lean_inc(v_getLevel_2862_);
lean_inc(v_inferType_2861_);
lean_inc(v_letValue_2860_);
lean_inc(v_proofInstInfoFVar_2859_);
lean_inc(v_proofInstInfo_2858_);
lean_inc(v_maxFVar_2857_);
lean_inc(v_share_2856_);
lean_dec(v___x_2855_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2933_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2873_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2873_);
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_maxFVar_2857_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_proofInstInfo_2858_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_proofInstInfoFVar_2859_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_letValue_2860_);
lean_ctor_set(v_reuseFailAlloc_2932_, 5, v_inferType_2861_);
lean_ctor_set(v_reuseFailAlloc_2932_, 6, v_getLevel_2862_);
lean_ctor_set(v_reuseFailAlloc_2932_, 7, v_congrInfo_2863_);
lean_ctor_set(v_reuseFailAlloc_2932_, 8, v_defEqI_2864_);
lean_ctor_set(v_reuseFailAlloc_2932_, 9, v_extensions_2865_);
lean_ctor_set(v_reuseFailAlloc_2932_, 10, v_issues_2866_);
lean_ctor_set(v_reuseFailAlloc_2932_, 11, v_canon_2867_);
lean_ctor_set(v_reuseFailAlloc_2932_, 12, v_instanceOverrides_2868_);
lean_ctor_set_uint8(v_reuseFailAlloc_2932_, sizeof(void*)*13, v_debug_2869_);
v___x_2875_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_st_ref_put(v_a_2853_, v___x_2875_);
v___x_2877_ = lean_apply_2(v_k_2851_, v_ctx_2852_, v_share_2856_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v_maxFVar_2881_; lean_object* v_proofInstInfo_2882_; lean_object* v_proofInstInfoFVar_2883_; lean_object* v_letValue_2884_; lean_object* v_inferType_2885_; lean_object* v_getLevel_2886_; lean_object* v_congrInfo_2887_; lean_object* v_defEqI_2888_; lean_object* v_extensions_2889_; lean_object* v_issues_2890_; lean_object* v_canon_2891_; lean_object* v_instanceOverrides_2892_; uint8_t v_debug_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2903_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
v_a_2879_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2877_, 2);
v___x_2880_ = lean_st_ref_take(v_a_2853_);
v_maxFVar_2881_ = lean_ctor_get(v___x_2880_, 1);
v_proofInstInfo_2882_ = lean_ctor_get(v___x_2880_, 2);
v_proofInstInfoFVar_2883_ = lean_ctor_get(v___x_2880_, 3);
v_letValue_2884_ = lean_ctor_get(v___x_2880_, 4);
v_inferType_2885_ = lean_ctor_get(v___x_2880_, 5);
v_getLevel_2886_ = lean_ctor_get(v___x_2880_, 6);
v_congrInfo_2887_ = lean_ctor_get(v___x_2880_, 7);
v_defEqI_2888_ = lean_ctor_get(v___x_2880_, 8);
v_extensions_2889_ = lean_ctor_get(v___x_2880_, 9);
v_issues_2890_ = lean_ctor_get(v___x_2880_, 10);
v_canon_2891_ = lean_ctor_get(v___x_2880_, 11);
v_instanceOverrides_2892_ = lean_ctor_get(v___x_2880_, 12);
v_debug_2893_ = lean_ctor_get_uint8(v___x_2880_, sizeof(void*)*13);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v___x_2880_, 0);
lean_dec(v_unused_2904_);
v___x_2895_ = v___x_2880_;
v_isShared_2896_ = v_isSharedCheck_2903_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_instanceOverrides_2892_);
lean_inc(v_canon_2891_);
lean_inc(v_issues_2890_);
lean_inc(v_extensions_2889_);
lean_inc(v_defEqI_2888_);
lean_inc(v_congrInfo_2887_);
lean_inc(v_getLevel_2886_);
lean_inc(v_inferType_2885_);
lean_inc(v_letValue_2884_);
lean_inc(v_proofInstInfoFVar_2883_);
lean_inc(v_proofInstInfo_2882_);
lean_inc(v_maxFVar_2881_);
lean_dec(v___x_2880_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2903_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v_a_2879_);
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2879_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_maxFVar_2881_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_proofInstInfo_2882_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_proofInstInfoFVar_2883_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_letValue_2884_);
lean_ctor_set(v_reuseFailAlloc_2902_, 5, v_inferType_2885_);
lean_ctor_set(v_reuseFailAlloc_2902_, 6, v_getLevel_2886_);
lean_ctor_set(v_reuseFailAlloc_2902_, 7, v_congrInfo_2887_);
lean_ctor_set(v_reuseFailAlloc_2902_, 8, v_defEqI_2888_);
lean_ctor_set(v_reuseFailAlloc_2902_, 9, v_extensions_2889_);
lean_ctor_set(v_reuseFailAlloc_2902_, 10, v_issues_2890_);
lean_ctor_set(v_reuseFailAlloc_2902_, 11, v_canon_2891_);
lean_ctor_set(v_reuseFailAlloc_2902_, 12, v_instanceOverrides_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, sizeof(void*)*13, v_debug_2893_);
v___x_2898_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_st_ref_put(v_a_2853_, v___x_2898_);
v___x_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_a_2878_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v_maxFVar_2908_; lean_object* v_proofInstInfo_2909_; lean_object* v_proofInstInfoFVar_2910_; lean_object* v_letValue_2911_; lean_object* v_inferType_2912_; lean_object* v_getLevel_2913_; lean_object* v_congrInfo_2914_; lean_object* v_defEqI_2915_; lean_object* v_extensions_2916_; lean_object* v_issues_2917_; lean_object* v_canon_2918_; lean_object* v_instanceOverrides_2919_; uint8_t v_debug_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2930_; 
v_a_2905_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2905_);
v_a_2906_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2877_, 2);
v___x_2907_ = lean_st_ref_take(v_a_2853_);
v_maxFVar_2908_ = lean_ctor_get(v___x_2907_, 1);
v_proofInstInfo_2909_ = lean_ctor_get(v___x_2907_, 2);
v_proofInstInfoFVar_2910_ = lean_ctor_get(v___x_2907_, 3);
v_letValue_2911_ = lean_ctor_get(v___x_2907_, 4);
v_inferType_2912_ = lean_ctor_get(v___x_2907_, 5);
v_getLevel_2913_ = lean_ctor_get(v___x_2907_, 6);
v_congrInfo_2914_ = lean_ctor_get(v___x_2907_, 7);
v_defEqI_2915_ = lean_ctor_get(v___x_2907_, 8);
v_extensions_2916_ = lean_ctor_get(v___x_2907_, 9);
v_issues_2917_ = lean_ctor_get(v___x_2907_, 10);
v_canon_2918_ = lean_ctor_get(v___x_2907_, 11);
v_instanceOverrides_2919_ = lean_ctor_get(v___x_2907_, 12);
v_debug_2920_ = lean_ctor_get_uint8(v___x_2907_, sizeof(void*)*13);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2930_ == 0)
{
lean_object* v_unused_2931_; 
v_unused_2931_ = lean_ctor_get(v___x_2907_, 0);
lean_dec(v_unused_2931_);
v___x_2922_ = v___x_2907_;
v_isShared_2923_ = v_isSharedCheck_2930_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_instanceOverrides_2919_);
lean_inc(v_canon_2918_);
lean_inc(v_issues_2917_);
lean_inc(v_extensions_2916_);
lean_inc(v_defEqI_2915_);
lean_inc(v_congrInfo_2914_);
lean_inc(v_getLevel_2913_);
lean_inc(v_inferType_2912_);
lean_inc(v_letValue_2911_);
lean_inc(v_proofInstInfoFVar_2910_);
lean_inc(v_proofInstInfo_2909_);
lean_inc(v_maxFVar_2908_);
lean_dec(v___x_2907_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2930_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v_a_2906_);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2906_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_maxFVar_2908_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_proofInstInfo_2909_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_proofInstInfoFVar_2910_);
lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_letValue_2911_);
lean_ctor_set(v_reuseFailAlloc_2929_, 5, v_inferType_2912_);
lean_ctor_set(v_reuseFailAlloc_2929_, 6, v_getLevel_2913_);
lean_ctor_set(v_reuseFailAlloc_2929_, 7, v_congrInfo_2914_);
lean_ctor_set(v_reuseFailAlloc_2929_, 8, v_defEqI_2915_);
lean_ctor_set(v_reuseFailAlloc_2929_, 9, v_extensions_2916_);
lean_ctor_set(v_reuseFailAlloc_2929_, 10, v_issues_2917_);
lean_ctor_set(v_reuseFailAlloc_2929_, 11, v_canon_2918_);
lean_ctor_set(v_reuseFailAlloc_2929_, 12, v_instanceOverrides_2919_);
lean_ctor_set_uint8(v_reuseFailAlloc_2929_, sizeof(void*)*13, v_debug_2920_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_st_ref_put(v_a_2853_, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_a_2905_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2934_, lean_object* v_ctx_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2934_, v_ctx_2935_, v_a_2936_);
lean_dec(v_a_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2939_, lean_object* v_k_2940_, lean_object* v_ctx_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2940_, v_ctx_2941_, v_a_2943_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2950_, lean_object* v_k_2951_, lean_object* v_ctx_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2950_, v_k_2951_, v_ctx_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2961_){
_start:
{
lean_object* v_config_2962_; lean_object* v_sharedExprs_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2980_; 
v_config_2962_ = lean_ctor_get(v_ctx_2961_, 1);
v_sharedExprs_2963_ = lean_ctor_get(v_ctx_2961_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_ctx_2961_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2965_ = v_ctx_2961_;
v_isShared_2966_ = v_isSharedCheck_2980_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_config_2962_);
lean_inc(v_sharedExprs_2963_);
lean_dec(v_ctx_2961_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2980_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
uint8_t v_verbose_2967_; uint8_t v_enforceUnfoldReducible_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2979_; 
v_verbose_2967_ = lean_ctor_get_uint8(v_config_2962_, 0);
v_enforceUnfoldReducible_2968_ = lean_ctor_get_uint8(v_config_2962_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_config_2962_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2970_ = v_config_2962_;
v_isShared_2971_ = v_isSharedCheck_2979_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v_config_2962_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2979_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v___x_2972_; lean_object* v___x_2974_; 
v___x_2972_ = 0;
if (v_isShared_2971_ == 0)
{
v___x_2974_ = v___x_2970_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, 0, v_verbose_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, 1, v_enforceUnfoldReducible_2968_);
v___x_2974_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
lean_ctor_set_uint8(v___x_2974_, 2, v___x_2972_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_2974_);
v___x_2976_ = v___x_2965_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_sharedExprs_2963_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2982_, lean_object* v_x_2983_){
_start:
{
lean_object* v___f_2984_; lean_object* v___x_2985_; 
v___f_2984_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2985_ = lean_apply_3(v_inst_2982_, lean_box(0), v___f_2984_, v_x_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2986_, lean_object* v_00_u03b1_2987_, lean_object* v_inst_2988_, lean_object* v_x_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2988_, v_x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2991_){
_start:
{
lean_object* v_config_2992_; lean_object* v_sharedExprs_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3009_; 
v_config_2992_ = lean_ctor_get(v_ctx_2991_, 1);
v_sharedExprs_2993_ = lean_ctor_get(v_ctx_2991_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_ctx_2991_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2995_ = v_ctx_2991_;
v_isShared_2996_ = v_isSharedCheck_3009_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_config_2992_);
lean_inc(v_sharedExprs_2993_);
lean_dec(v_ctx_2991_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3009_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v_verbose_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3008_; 
v_verbose_2997_ = lean_ctor_get_uint8(v_config_2992_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_config_2992_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2999_ = v_config_2992_;
v_isShared_3000_ = v_isSharedCheck_3008_;
goto v_resetjp_2998_;
}
else
{
lean_dec(v_config_2992_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3008_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
uint8_t v___x_3001_; lean_object* v___x_3003_; 
v___x_3001_ = 0;
if (v_isShared_3000_ == 0)
{
v___x_3003_ = v___x_2999_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3007_, 0, v_verbose_2997_);
v___x_3003_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
lean_ctor_set_uint8(v___x_3003_, 1, v___x_3001_);
lean_ctor_set_uint8(v___x_3003_, 2, v___x_3001_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_3003_);
v___x_3005_ = v___x_2995_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_sharedExprs_2993_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v___f_3013_; lean_object* v___x_3014_; 
v___f_3013_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_3014_ = lean_apply_3(v_inst_3011_, lean_box(0), v___f_3013_, v_x_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_3015_, lean_object* v_00_u03b1_3016_, lean_object* v_inst_3017_, lean_object* v_x_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_3017_, v_x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_config_3023_; lean_object* v___x_3024_; lean_object* v_env_3025_; uint8_t v_enforceUnfoldReducible_3026_; uint8_t v_enforceFoldProjs_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v_config_3023_ = lean_ctor_get(v_a_3020_, 1);
v___x_3024_ = lean_st_ref_get(v_a_3021_);
v_env_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc_ref(v_env_3025_);
lean_dec(v___x_3024_);
v_enforceUnfoldReducible_3026_ = lean_ctor_get_uint8(v_config_3023_, 1);
v_enforceFoldProjs_3027_ = lean_ctor_get_uint8(v_config_3023_, 2);
v___x_3028_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3028_, 0, v_env_3025_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*1, v_enforceUnfoldReducible_3026_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*1 + 1, v_enforceFoldProjs_3027_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3034_, v_a_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_config_3057_; uint8_t v_enforceUnfoldReducible_3058_; uint8_t v_enforceFoldProjs_3059_; lean_object* v_e_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v_e_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; 
v_config_3057_ = lean_ctor_get(v_a_3051_, 1);
v_enforceUnfoldReducible_3058_ = lean_ctor_get_uint8(v_config_3057_, 1);
v_enforceFoldProjs_3059_ = lean_ctor_get_uint8(v_config_3057_, 2);
if (v_enforceUnfoldReducible_3058_ == 0)
{
v_e_3069_ = v_e_3050_;
v___y_3070_ = v_a_3052_;
v___y_3071_ = v_a_3053_;
v___y_3072_ = v_a_3054_;
v___y_3073_ = v_a_3055_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3050_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v_e_3069_ = v_a_3077_;
v___y_3070_ = v_a_3052_;
v___y_3071_ = v_a_3053_;
v___y_3072_ = v_a_3054_;
v___y_3073_ = v_a_3055_;
goto v___jp_3068_;
}
else
{
return v___x_3076_;
}
}
v___jp_3060_:
{
if (v_enforceUnfoldReducible_3058_ == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v_e_3061_);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3067_;
}
}
v___jp_3068_:
{
if (v_enforceFoldProjs_3059_ == 0)
{
v_e_3061_ = v_e_3069_;
v___y_3062_ = v___y_3070_;
v___y_3063_ = v___y_3071_;
v___y_3064_ = v___y_3072_;
v___y_3065_ = v___y_3073_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Meta_Sym_foldProjs(v_e_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
v_e_3061_ = v_a_3075_;
v___y_3062_ = v___y_3070_;
v___y_3063_ = v___y_3071_;
v___y_3064_ = v___y_3072_;
v___y_3065_ = v___y_3073_;
goto v___jp_3060_;
}
else
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec_ref(v_a_3079_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3086_, v_a_3087_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
return v_res_3103_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_instMonadEIO___redArg();
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_toApplicative_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3182_; 
v___x_3117_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3118_ = l_StateRefT_x27_instMonad___redArg(v___x_3117_);
v_toApplicative_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v___x_3118_, 1);
lean_dec(v_unused_3183_);
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3182_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_toApplicative_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3182_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_toFunctor_3123_; lean_object* v_toSeq_3124_; lean_object* v_toSeqLeft_3125_; lean_object* v_toSeqRight_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3180_; 
v_toFunctor_3123_ = lean_ctor_get(v_toApplicative_3119_, 0);
v_toSeq_3124_ = lean_ctor_get(v_toApplicative_3119_, 2);
v_toSeqLeft_3125_ = lean_ctor_get(v_toApplicative_3119_, 3);
v_toSeqRight_3126_ = lean_ctor_get(v_toApplicative_3119_, 4);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_toApplicative_3119_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v_toApplicative_3119_, 1);
lean_dec(v_unused_3181_);
v___x_3128_ = v_toApplicative_3119_;
v_isShared_3129_ = v_isSharedCheck_3180_;
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
v_isShared_3129_ = v_isSharedCheck_3180_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___f_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___f_3136_; lean_object* v___f_3137_; lean_object* v___x_3139_; 
v___f_3130_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3131_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
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
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___f_3130_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v___f_3137_);
lean_ctor_set(v_reuseFailAlloc_3179_, 3, v___f_3136_);
lean_ctor_set(v_reuseFailAlloc_3179_, 4, v___f_3135_);
v___x_3139_ = v_reuseFailAlloc_3179_;
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
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v___f_3131_);
v___x_3141_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v_toApplicative_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3176_; 
v___x_3142_ = l_StateRefT_x27_instMonad___redArg(v___x_3141_);
v_toApplicative_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v___x_3142_, 1);
lean_dec(v_unused_3177_);
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3176_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_toApplicative_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3176_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_toFunctor_3147_; lean_object* v_toSeq_3148_; lean_object* v_toSeqLeft_3149_; lean_object* v_toSeqRight_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3174_; 
v_toFunctor_3147_ = lean_ctor_get(v_toApplicative_3143_, 0);
v_toSeq_3148_ = lean_ctor_get(v_toApplicative_3143_, 2);
v_toSeqLeft_3149_ = lean_ctor_get(v_toApplicative_3143_, 3);
v_toSeqRight_3150_ = lean_ctor_get(v_toApplicative_3143_, 4);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_toApplicative_3143_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_toApplicative_3143_, 1);
lean_dec(v_unused_3175_);
v___x_3152_ = v_toApplicative_3143_;
v_isShared_3153_ = v_isSharedCheck_3174_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_toSeqRight_3150_);
lean_inc(v_toSeqLeft_3149_);
lean_inc(v_toSeq_3148_);
lean_inc(v_toFunctor_3147_);
lean_dec(v_toApplicative_3143_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3174_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___f_3154_; lean_object* v___f_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___f_3159_; lean_object* v___f_3160_; lean_object* v___f_3161_; lean_object* v___x_3163_; 
v___f_3154_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3155_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3147_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toFunctor_3147_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toFunctor_3147_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___f_3156_);
lean_ctor_set(v___x_3158_, 1, v___f_3157_);
v___f_3159_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3159_, 0, v_toSeqRight_3150_);
v___f_3160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3160_, 0, v_toSeqLeft_3149_);
v___f_3161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3161_, 0, v_toSeq_3148_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 4, v___f_3159_);
lean_ctor_set(v___x_3152_, 3, v___f_3160_);
lean_ctor_set(v___x_3152_, 2, v___f_3161_);
lean_ctor_set(v___x_3152_, 1, v___f_3154_);
lean_ctor_set(v___x_3152_, 0, v___x_3158_);
v___x_3163_ = v___x_3152_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___f_3154_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v___f_3161_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v___f_3160_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v___f_3159_);
v___x_3163_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3165_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___f_3155_);
lean_ctor_set(v___x_3145_, 0, v___x_3163_);
v___x_3165_ = v___x_3145_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___f_3155_);
v___x_3165_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___f_3169_; lean_object* v___x_922__overap_3170_; lean_object* v___x_3171_; 
v___x_3166_ = l_StateRefT_x27_instMonad___redArg(v___x_3165_);
v___x_3167_ = l_Lean_instInhabitedExpr;
v___x_3168_ = l_instInhabitedOfMonad___redArg(v___x_3166_, v___x_3167_);
v___f_3169_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3169_, 0, v___x_3168_);
v___x_922__overap_3170_ = lean_panic_fn_borrowed(v___f_3169_, v_msg_3109_);
lean_dec_ref(v___f_3169_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
lean_inc_ref(v___y_3112_);
lean_inc(v___y_3111_);
lean_inc_ref(v___y_3110_);
v___x_3171_ = lean_apply_7(v___x_922__overap_3170_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, lean_box(0));
return v___x_3171_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3193_, lean_object* v_vals_3194_, lean_object* v_i_3195_, lean_object* v_k_3196_){
_start:
{
lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = lean_array_get_size(v_keys_3193_);
v___x_3198_ = lean_nat_dec_lt(v_i_3195_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
lean_dec(v_i_3195_);
v___x_3199_ = lean_box(0);
return v___x_3199_;
}
else
{
lean_object* v_k_x27_3200_; uint8_t v___x_3201_; 
v_k_x27_3200_ = lean_array_fget_borrowed(v_keys_3193_, v_i_3195_);
v___x_3201_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3196_, v_k_x27_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_unsigned_to_nat(1u);
v___x_3203_ = lean_nat_add(v_i_3195_, v___x_3202_);
lean_dec(v_i_3195_);
v_i_3195_ = v___x_3203_;
goto _start;
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_array_fget_borrowed(v_vals_3194_, v_i_3195_);
lean_dec(v_i_3195_);
lean_inc(v___x_3205_);
lean_inc(v_k_x27_3200_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_k_x27_3200_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3208_, lean_object* v_vals_3209_, lean_object* v_i_3210_, lean_object* v_k_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3208_, v_vals_3209_, v_i_3210_, v_k_3211_);
lean_dec_ref(v_k_3211_);
lean_dec_ref(v_vals_3209_);
lean_dec_ref(v_keys_3208_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3213_, size_t v_x_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 0)
{
lean_object* v_es_3216_; lean_object* v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; lean_object* v_j_3220_; lean_object* v___x_3221_; 
v_es_3216_ = lean_ctor_get(v_x_3213_, 0);
v___x_3217_ = lean_box(2);
v___x_3218_ = ((size_t)31ULL);
v___x_3219_ = lean_usize_land(v_x_3214_, v___x_3218_);
v_j_3220_ = lean_usize_to_nat(v___x_3219_);
v___x_3221_ = lean_array_get_borrowed(v___x_3217_, v_es_3216_, v_j_3220_);
lean_dec(v_j_3220_);
switch(lean_obj_tag(v___x_3221_))
{
case 0:
{
lean_object* v_key_3222_; lean_object* v_val_3223_; uint8_t v___x_3224_; 
v_key_3222_ = lean_ctor_get(v___x_3221_, 0);
v_val_3223_ = lean_ctor_get(v___x_3221_, 1);
v___x_3224_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3215_, v_key_3222_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_box(0);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_inc(v_val_3223_);
lean_inc(v_key_3222_);
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_key_3222_);
lean_ctor_set(v___x_3226_, 1, v_val_3223_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
case 1:
{
lean_object* v_node_3228_; size_t v___x_3229_; size_t v___x_3230_; 
v_node_3228_ = lean_ctor_get(v___x_3221_, 0);
v___x_3229_ = ((size_t)5ULL);
v___x_3230_ = lean_usize_shift_right(v_x_3214_, v___x_3229_);
v_x_3213_ = v_node_3228_;
v_x_3214_ = v___x_3230_;
goto _start;
}
default: 
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_box(0);
return v___x_3232_;
}
}
}
else
{
lean_object* v_ks_3233_; lean_object* v_vs_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v_ks_3233_ = lean_ctor_get(v_x_3213_, 0);
v_vs_3234_ = lean_ctor_get(v_x_3213_, 1);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3233_, v_vs_3234_, v___x_3235_, v_x_3215_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3237_, lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
size_t v_x_1244__boxed_3240_; lean_object* v_res_3241_; 
v_x_1244__boxed_3240_ = lean_unbox_usize(v_x_3238_);
lean_dec(v_x_3238_);
v_res_3241_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3237_, v_x_1244__boxed_3240_, v_x_3239_);
lean_dec_ref(v_x_3239_);
lean_dec_ref(v_x_3237_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3242_, lean_object* v_x_3243_){
_start:
{
uint64_t v___x_3244_; size_t v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3243_);
v___x_3245_ = lean_uint64_to_usize(v___x_3244_);
v___x_3246_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3242_, v___x_3245_, v_x_3243_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3247_, v_x_3248_);
lean_dec_ref(v_x_3248_);
lean_dec_ref(v_x_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3250_, lean_object* v_cache_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3253_, v_e_3250_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v_cache_3251_);
lean_ctor_set(v___x_3255_, 1, v___y_3253_);
v___x_3256_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3250_, v___y_3252_, v___x_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3266_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 1);
v_a_3258_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3260_ = v___x_3256_;
v_isShared_3261_ = v_isSharedCheck_3266_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3257_);
lean_inc(v_a_3258_);
lean_dec(v___x_3256_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3266_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_set_3262_; lean_object* v___x_3264_; 
v_set_3262_ = lean_ctor_get(v_a_3257_, 1);
lean_inc_ref(v_set_3262_);
lean_dec(v_a_3257_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v_set_3262_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3258_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_set_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3276_; 
v_a_3267_ = lean_ctor_get(v___x_3256_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v___x_3256_, 0);
lean_dec(v_unused_3277_);
v___x_3269_ = v___x_3256_;
v_isShared_3270_ = v_isSharedCheck_3276_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3256_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3276_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v_map_3271_; lean_object* v_set_3272_; lean_object* v___x_3274_; 
v_map_3271_ = lean_ctor_get(v_a_3267_, 0);
lean_inc_ref(v_map_3271_);
v_set_3272_ = lean_ctor_get(v_a_3267_, 1);
lean_inc_ref(v_set_3272_);
lean_dec(v_a_3267_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v_set_3272_);
lean_ctor_set(v___x_3269_, 0, v_map_3271_);
v___x_3274_ = v___x_3269_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_map_3271_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_set_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
else
{
lean_object* v_val_3278_; lean_object* v_fst_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v_cache_3251_);
lean_dec_ref(v_e_3250_);
v_val_3278_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_val_3278_);
lean_dec_ref_known(v___x_3254_, 1);
v_fst_3279_ = lean_ctor_get(v_val_3278_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_val_3278_);
if (v_isSharedCheck_3286_ == 0)
{
lean_object* v_unused_3287_; 
v_unused_3287_ = lean_ctor_get(v_val_3278_, 1);
lean_dec(v_unused_3287_);
v___x_3281_ = v_val_3278_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_fst_3279_);
lean_dec(v_val_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v___y_3253_);
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_fst_3279_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___y_3253_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3288_, lean_object* v_cache_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3288_, v_cache_3289_, v___y_3290_, v___y_3291_);
lean_dec_ref(v___y_3290_);
return v_res_3292_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3294_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3295_ = lean_unsigned_to_nat(16u);
v___x_3296_ = lean_unsigned_to_nat(401u);
v___x_3297_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3298_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_3299_ = l_mkPanicMessageWithDecl(v___x_3298_, v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3300_, lean_object* v_cache_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___f_3309_; lean_object* v___x_3310_; lean_object* v_env_3311_; uint8_t v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3325_; 
v___f_3309_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3309_, 0, v_e_3300_);
lean_closure_set(v___f_3309_, 1, v_cache_3301_);
v___x_3310_ = lean_st_ref_get(v_a_3307_);
v_env_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc_ref(v_env_3311_);
lean_dec(v___x_3310_);
v___x_3312_ = 0;
v___x_3313_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3313_, 0, v_env_3311_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*1, v___x_3312_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*1 + 1, v___x_3312_);
v___x_3314_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3309_, v___x_3313_, v_a_3303_);
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3325_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3325_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
if (lean_obj_tag(v_a_3315_) == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec_ref_known(v_a_3315_, 1);
lean_del_object(v___x_3317_);
v___x_3319_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3320_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3319_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
return v___x_3320_;
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; 
v_a_3321_ = lean_ctor_get(v_a_3315_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v_a_3315_, 1);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v_a_3321_);
v___x_3323_ = v___x_3317_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3326_, lean_object* v_cache_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3326_, v_cache_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3337_, v_x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3340_, v_x_3341_, v_x_3342_);
lean_dec_ref(v_x_3342_);
lean_dec_ref(v_x_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3344_, lean_object* v_x_3345_, size_t v_x_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3345_, v_x_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3349_, lean_object* v_x_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_){
_start:
{
size_t v_x_1449__boxed_3353_; lean_object* v_res_3354_; 
v_x_1449__boxed_3353_ = lean_unbox_usize(v_x_3351_);
lean_dec(v_x_3351_);
v_res_3354_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3349_, v_x_3350_, v_x_1449__boxed_3353_, v_x_3352_);
lean_dec_ref(v_x_3352_);
lean_dec_ref(v_x_3350_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3355_, lean_object* v_keys_3356_, lean_object* v_vals_3357_, lean_object* v_heq_3358_, lean_object* v_i_3359_, lean_object* v_k_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3356_, v_vals_3357_, v_i_3359_, v_k_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3362_, lean_object* v_keys_3363_, lean_object* v_vals_3364_, lean_object* v_heq_3365_, lean_object* v_i_3366_, lean_object* v_k_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3362_, v_keys_3363_, v_vals_3364_, v_heq_3365_, v_i_3366_, v_k_3367_);
lean_dec_ref(v_k_3367_);
lean_dec_ref(v_vals_3364_);
lean_dec_ref(v_keys_3363_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg(lean_object* v_e_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v_share_3373_; lean_object* v___x_3374_; 
v___x_3372_ = lean_st_ref_get(v_a_3370_);
v_share_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc_ref(v_share_3373_);
lean_dec(v___x_3372_);
v___x_3374_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_share_3373_, v_e_3369_);
lean_dec_ref(v_share_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = 0;
v___x_3376_ = lean_box(v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
else
{
lean_object* v_val_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3390_; 
v_val_3378_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3380_ = v___x_3374_;
v_isShared_3381_ = v_isSharedCheck_3390_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_val_3378_);
lean_dec(v___x_3374_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3390_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v_fst_3382_; size_t v___x_3383_; size_t v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v_fst_3382_ = lean_ctor_get(v_val_3378_, 0);
lean_inc(v_fst_3382_);
lean_dec(v_val_3378_);
v___x_3383_ = lean_ptr_addr(v_fst_3382_);
lean_dec(v_fst_3382_);
v___x_3384_ = lean_ptr_addr(v_e_3369_);
v___x_3385_ = lean_usize_dec_eq(v___x_3383_, v___x_3384_);
v___x_3386_ = lean_box(v___x_3385_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3386_);
v___x_3388_ = v___x_3380_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg___boxed(lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_e_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_e_3391_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared(lean_object* v_e_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_e_3395_, v_a_3397_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___boxed(lean_object* v_e_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_Meta_Sym_isMaxShared(v_e_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec_ref(v_e_3404_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_ref_3419_; lean_object* v___x_3420_; lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3429_; 
v_ref_3419_ = lean_ctor_get(v___y_3416_, 2);
v___x_3420_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
lean_inc(v_ref_3419_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v_ref_3419_);
lean_ctor_set(v___x_3425_, 1, v_a_3421_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 1);
lean_ctor_set(v___x_3423_, 0, v___x_3425_);
v___x_3427_ = v___x_3423_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3439_ = l_Lean_stringToMessageData(v___x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3440_, lean_object* v_cache_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___x_3459_; 
v___x_3459_ = l_Lean_Expr_hasLooseBVars(v_e_3440_);
if (v___x_3459_ == 0)
{
v___y_3450_ = v_a_3442_;
v___y_3451_ = v_a_3443_;
v___y_3452_ = v_a_3444_;
v___y_3453_ = v_a_3445_;
v___y_3454_ = v_a_3446_;
v___y_3455_ = v_a_3447_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v_cache_3441_);
v___x_3460_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3461_ = l_Lean_indentExpr(v_e_3440_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3462_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
v___jp_3449_:
{
lean_object* v___x_3456_; 
v___x_3456_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3440_, v___y_3450_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3457_, v_cache_3441_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
return v___x_3458_;
}
else
{
lean_dec_ref(v_cache_3441_);
return v___x_3456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3472_, lean_object* v_cache_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3472_, v_cache_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3482_, lean_object* v_msg_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3483_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3492_, lean_object* v_msg_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3492_, v_msg_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3502_, lean_object* v___x_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3505_, v_e_3502_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3503_);
lean_ctor_set(v___x_3507_, 1, v___y_3505_);
v___x_3508_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3502_, v___y_3504_, v___x_3507_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3518_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 1);
v_a_3510_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3512_ = v___x_3508_;
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3509_);
lean_inc(v_a_3510_);
lean_dec(v___x_3508_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_set_3514_; lean_object* v___x_3516_; 
v_set_3514_ = lean_ctor_get(v_a_3509_, 1);
lean_inc_ref(v_set_3514_);
lean_dec(v_a_3509_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 1, v_set_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3510_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_set_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3528_; 
v_a_3519_ = lean_ctor_get(v___x_3508_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v___x_3508_, 0);
lean_dec(v_unused_3529_);
v___x_3521_ = v___x_3508_;
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3508_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_map_3523_; lean_object* v_set_3524_; lean_object* v___x_3526_; 
v_map_3523_ = lean_ctor_get(v_a_3519_, 0);
lean_inc_ref(v_map_3523_);
v_set_3524_ = lean_ctor_get(v_a_3519_, 1);
lean_inc_ref(v_set_3524_);
lean_dec(v_a_3519_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v_set_3524_);
lean_ctor_set(v___x_3521_, 0, v_map_3523_);
v___x_3526_ = v___x_3521_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_map_3523_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_set_3524_);
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
else
{
lean_object* v_val_3530_; lean_object* v_fst_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v___x_3503_);
lean_dec_ref(v_e_3502_);
v_val_3530_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_val_3530_);
lean_dec_ref_known(v___x_3506_, 1);
v_fst_3531_ = lean_ctor_get(v_val_3530_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_val_3530_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v_val_3530_, 1);
lean_dec(v_unused_3539_);
v___x_3533_ = v_val_3530_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_fst_3531_);
lean_dec(v_val_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 1, v___y_3505_);
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_fst_3531_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___y_3505_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3540_, lean_object* v___x_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3540_, v___x_3541_, v___y_3542_, v___y_3543_);
lean_dec_ref(v___y_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3553_; lean_object* v_a_3554_; lean_object* v___x_3555_; lean_object* v___f_3556_; lean_object* v___x_3557_; lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3568_; 
v___x_3553_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3546_, v_a_3551_);
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref(v___x_3553_);
v___x_3555_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
lean_inc_ref(v_e_3545_);
v___f_3556_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3556_, 0, v_e_3545_);
lean_closure_set(v___f_3556_, 1, v___x_3555_);
v___x_3557_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3556_, v_a_3554_, v_a_3547_);
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
if (lean_obj_tag(v_a_3558_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
lean_del_object(v___x_3560_);
v_a_3562_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v_a_3558_, 1);
v___x_3563_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3545_, v_a_3562_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
return v___x_3563_;
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; 
lean_dec_ref(v_e_3545_);
v_a_3564_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v_a_3558_, 1);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_a_3564_);
v___x_3566_ = v___x_3560_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Meta_Sym_shareCommon(v_e_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3578_, v___y_3579_, v___y_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3582_, v___y_3583_, v___y_3584_);
lean_dec_ref(v___y_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v___f_3594_; lean_object* v___x_3595_; lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3608_; 
lean_inc_ref(v_e_3586_);
v___f_3594_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3594_, 0, v_e_3586_);
v___x_3595_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3587_, v_a_3592_);
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
v___x_3597_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3594_, v_a_3596_, v_a_3588_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3608_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3608_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_a_3598_) == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref_known(v_a_3598_, 1);
lean_del_object(v___x_3600_);
v___x_3602_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_3603_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3586_, v___x_3602_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
return v___x_3603_;
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; 
lean_dec_ref(v_e_3586_);
v_a_3604_ = lean_ctor_get(v_a_3598_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v_a_3598_, 1);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_a_3604_);
v___x_3606_ = v___x_3600_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3618_, lean_object* v_vals_3619_, lean_object* v_i_3620_, lean_object* v_k_3621_){
_start:
{
lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = lean_array_get_size(v_keys_3618_);
v___x_3623_ = lean_nat_dec_lt(v_i_3620_, v___x_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_dec(v_i_3620_);
v___x_3624_ = lean_box(0);
return v___x_3624_;
}
else
{
lean_object* v_k_x27_3625_; uint8_t v___x_3626_; 
v_k_x27_3625_ = lean_array_fget_borrowed(v_keys_3618_, v_i_3620_);
v___x_3626_ = l_Lean_instBEqFVarId_beq(v_k_3621_, v_k_x27_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = lean_unsigned_to_nat(1u);
v___x_3628_ = lean_nat_add(v_i_3620_, v___x_3627_);
lean_dec(v_i_3620_);
v_i_3620_ = v___x_3628_;
goto _start;
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_array_fget_borrowed(v_vals_3619_, v_i_3620_);
lean_dec(v_i_3620_);
lean_inc(v___x_3630_);
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3632_, lean_object* v_vals_3633_, lean_object* v_i_3634_, lean_object* v_k_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3632_, v_vals_3633_, v_i_3634_, v_k_3635_);
lean_dec(v_k_3635_);
lean_dec_ref(v_vals_3633_);
lean_dec_ref(v_keys_3632_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(lean_object* v_x_3637_, size_t v_x_3638_, lean_object* v_x_3639_){
_start:
{
if (lean_obj_tag(v_x_3637_) == 0)
{
lean_object* v_es_3640_; lean_object* v___x_3641_; size_t v___x_3642_; size_t v___x_3643_; lean_object* v_j_3644_; lean_object* v___x_3645_; 
v_es_3640_ = lean_ctor_get(v_x_3637_, 0);
v___x_3641_ = lean_box(2);
v___x_3642_ = ((size_t)31ULL);
v___x_3643_ = lean_usize_land(v_x_3638_, v___x_3642_);
v_j_3644_ = lean_usize_to_nat(v___x_3643_);
v___x_3645_ = lean_array_get_borrowed(v___x_3641_, v_es_3640_, v_j_3644_);
lean_dec(v_j_3644_);
switch(lean_obj_tag(v___x_3645_))
{
case 0:
{
lean_object* v_key_3646_; lean_object* v_val_3647_; uint8_t v___x_3648_; 
v_key_3646_ = lean_ctor_get(v___x_3645_, 0);
v_val_3647_ = lean_ctor_get(v___x_3645_, 1);
v___x_3648_ = l_Lean_instBEqFVarId_beq(v_x_3639_, v_key_3646_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_box(0);
return v___x_3649_;
}
else
{
lean_object* v___x_3650_; 
lean_inc(v_val_3647_);
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_val_3647_);
return v___x_3650_;
}
}
case 1:
{
lean_object* v_node_3651_; size_t v___x_3652_; size_t v___x_3653_; 
v_node_3651_ = lean_ctor_get(v___x_3645_, 0);
v___x_3652_ = ((size_t)5ULL);
v___x_3653_ = lean_usize_shift_right(v_x_3638_, v___x_3652_);
v_x_3637_ = v_node_3651_;
v_x_3638_ = v___x_3653_;
goto _start;
}
default: 
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_box(0);
return v___x_3655_;
}
}
}
else
{
lean_object* v_ks_3656_; lean_object* v_vs_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_ks_3656_ = lean_ctor_get(v_x_3637_, 0);
v_vs_3657_ = lean_ctor_get(v_x_3637_, 1);
v___x_3658_ = lean_unsigned_to_nat(0u);
v___x_3659_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3656_, v_vs_3657_, v___x_3658_, v_x_3639_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
size_t v_x_4130__boxed_3663_; lean_object* v_res_3664_; 
v_x_4130__boxed_3663_ = lean_unbox_usize(v_x_3661_);
lean_dec(v_x_3661_);
v_res_3664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3660_, v_x_4130__boxed_3663_, v_x_3662_);
lean_dec(v_x_3662_);
lean_dec_ref(v_x_3660_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(lean_object* v_x_3665_, lean_object* v_x_3666_){
_start:
{
uint64_t v___x_3667_; size_t v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = l_Lean_instHashableFVarId_hash(v_x_3666_);
v___x_3668_ = lean_uint64_to_usize(v___x_3667_);
v___x_3669_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3665_, v___x_3668_, v_x_3666_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg___boxed(lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_x_3670_, v_x_3671_);
lean_dec(v_x_3671_);
lean_dec_ref(v_x_3670_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_, lean_object* v_x_3676_){
_start:
{
lean_object* v_ks_3677_; lean_object* v_vs_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3702_; 
v_ks_3677_ = lean_ctor_get(v_x_3673_, 0);
v_vs_3678_ = lean_ctor_get(v_x_3673_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_x_3673_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3680_ = v_x_3673_;
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_vs_3678_);
lean_inc(v_ks_3677_);
lean_dec(v_x_3673_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; uint8_t v___x_3683_; 
v___x_3682_ = lean_array_get_size(v_ks_3677_);
v___x_3683_ = lean_nat_dec_lt(v_x_3674_, v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_dec(v_x_3674_);
v___x_3684_ = lean_array_push(v_ks_3677_, v_x_3675_);
v___x_3685_ = lean_array_push(v_vs_3678_, v_x_3676_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3685_);
lean_ctor_set(v___x_3680_, 0, v___x_3684_);
v___x_3687_ = v___x_3680_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
else
{
lean_object* v_k_x27_3689_; uint8_t v___x_3690_; 
v_k_x27_3689_ = lean_array_fget_borrowed(v_ks_3677_, v_x_3674_);
v___x_3690_ = l_Lean_instBEqFVarId_beq(v_x_3675_, v_k_x27_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3692_; 
if (v_isShared_3681_ == 0)
{
v___x_3692_ = v___x_3680_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_ks_3677_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_vs_3678_);
v___x_3692_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_add(v_x_3674_, v___x_3693_);
lean_dec(v_x_3674_);
v_x_3673_ = v___x_3692_;
v_x_3674_ = v___x_3694_;
goto _start;
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3697_ = lean_array_fset(v_ks_3677_, v_x_3674_, v_x_3675_);
v___x_3698_ = lean_array_fset(v_vs_3678_, v_x_3674_, v_x_3676_);
lean_dec(v_x_3674_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v___x_3698_);
lean_ctor_set(v___x_3680_, 0, v___x_3697_);
v___x_3700_ = v___x_3680_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_3703_, lean_object* v_k_3704_, lean_object* v_v_3705_){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_3703_, v___x_3706_, v_k_3704_, v_v_3705_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(lean_object* v_x_3709_, size_t v_x_3710_, size_t v_x_3711_, lean_object* v_x_3712_, lean_object* v_x_3713_){
_start:
{
if (lean_obj_tag(v_x_3709_) == 0)
{
lean_object* v_es_3714_; size_t v___x_3715_; size_t v___x_3716_; lean_object* v_j_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_es_3714_ = lean_ctor_get(v_x_3709_, 0);
v___x_3715_ = ((size_t)31ULL);
v___x_3716_ = lean_usize_land(v_x_3710_, v___x_3715_);
v_j_3717_ = lean_usize_to_nat(v___x_3716_);
v___x_3718_ = lean_array_get_size(v_es_3714_);
v___x_3719_ = lean_nat_dec_lt(v_j_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_dec(v_j_3717_);
lean_dec(v_x_3713_);
lean_dec(v_x_3712_);
return v_x_3709_;
}
else
{
lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3758_; 
lean_inc_ref(v_es_3714_);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_x_3709_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v_x_3709_, 0);
lean_dec(v_unused_3759_);
v___x_3721_ = v_x_3709_;
v_isShared_3722_ = v_isSharedCheck_3758_;
goto v_resetjp_3720_;
}
else
{
lean_dec(v_x_3709_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3758_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v_v_3723_; lean_object* v___x_3724_; lean_object* v_xs_x27_3725_; lean_object* v___y_3727_; 
v_v_3723_ = lean_array_fget(v_es_3714_, v_j_3717_);
v___x_3724_ = lean_box(0);
v_xs_x27_3725_ = lean_array_fset(v_es_3714_, v_j_3717_, v___x_3724_);
switch(lean_obj_tag(v_v_3723_))
{
case 0:
{
lean_object* v_key_3732_; lean_object* v_val_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3743_; 
v_key_3732_ = lean_ctor_get(v_v_3723_, 0);
v_val_3733_ = lean_ctor_get(v_v_3723_, 1);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_v_3723_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3735_ = v_v_3723_;
v_isShared_3736_ = v_isSharedCheck_3743_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_val_3733_);
lean_inc(v_key_3732_);
lean_dec(v_v_3723_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3743_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
uint8_t v___x_3737_; 
v___x_3737_ = l_Lean_instBEqFVarId_beq(v_x_3712_, v_key_3732_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_del_object(v___x_3735_);
v___x_3738_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3732_, v_val_3733_, v_x_3712_, v_x_3713_);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
v___y_3727_ = v___x_3739_;
goto v___jp_3726_;
}
else
{
lean_object* v___x_3741_; 
lean_dec(v_val_3733_);
lean_dec(v_key_3732_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 1, v_x_3713_);
lean_ctor_set(v___x_3735_, 0, v_x_3712_);
v___x_3741_ = v___x_3735_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_x_3712_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_x_3713_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
v___y_3727_ = v___x_3741_;
goto v___jp_3726_;
}
}
}
}
case 1:
{
lean_object* v_node_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3756_; 
v_node_3744_ = lean_ctor_get(v_v_3723_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_v_3723_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3746_ = v_v_3723_;
v_isShared_3747_ = v_isSharedCheck_3756_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_node_3744_);
lean_dec(v_v_3723_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3756_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
size_t v___x_3748_; size_t v___x_3749_; size_t v___x_3750_; size_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3748_ = ((size_t)5ULL);
v___x_3749_ = lean_usize_shift_right(v_x_3710_, v___x_3748_);
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_add(v_x_3711_, v___x_3750_);
v___x_3752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_node_3744_, v___x_3749_, v___x_3751_, v_x_3712_, v_x_3713_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v___x_3752_);
v___x_3754_ = v___x_3746_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
v___y_3727_ = v___x_3754_;
goto v___jp_3726_;
}
}
}
default: 
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_x_3712_);
lean_ctor_set(v___x_3757_, 1, v_x_3713_);
v___y_3727_ = v___x_3757_;
goto v___jp_3726_;
}
}
v___jp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = lean_array_fset(v_xs_x27_3725_, v_j_3717_, v___y_3727_);
lean_dec(v_j_3717_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3728_);
v___x_3730_ = v___x_3721_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
else
{
lean_object* v_ks_3760_; lean_object* v_vs_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3779_; 
v_ks_3760_ = lean_ctor_get(v_x_3709_, 0);
v_vs_3761_ = lean_ctor_get(v_x_3709_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_x_3709_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3763_ = v_x_3709_;
v_isShared_3764_ = v_isSharedCheck_3779_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_vs_3761_);
lean_inc(v_ks_3760_);
lean_dec(v_x_3709_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3779_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_ks_3760_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_vs_3761_);
v___x_3766_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v_newNode_3767_; size_t v___x_3768_; uint8_t v___x_3769_; 
v_newNode_3767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(v___x_3766_, v_x_3712_, v_x_3713_);
v___x_3768_ = ((size_t)7ULL);
v___x_3769_ = lean_usize_dec_le(v___x_3768_, v_x_3711_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3770_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3767_);
v___x_3771_ = lean_unsigned_to_nat(4u);
v___x_3772_ = lean_nat_dec_lt(v___x_3770_, v___x_3771_);
lean_dec(v___x_3770_);
if (v___x_3772_ == 0)
{
lean_object* v_ks_3773_; lean_object* v_vs_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_ks_3773_ = lean_ctor_get(v_newNode_3767_, 0);
lean_inc_ref(v_ks_3773_);
v_vs_3774_ = lean_ctor_get(v_newNode_3767_, 1);
lean_inc_ref(v_vs_3774_);
lean_dec_ref(v_newNode_3767_);
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0);
v___x_3777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_x_3711_, v_ks_3773_, v_vs_3774_, v___x_3775_, v___x_3776_);
lean_dec_ref(v_vs_3774_);
lean_dec_ref(v_ks_3773_);
return v___x_3777_;
}
else
{
return v_newNode_3767_;
}
}
else
{
return v_newNode_3767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_3780_, lean_object* v_keys_3781_, lean_object* v_vals_3782_, lean_object* v_i_3783_, lean_object* v_entries_3784_){
_start:
{
lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3785_ = lean_array_get_size(v_keys_3781_);
v___x_3786_ = lean_nat_dec_lt(v_i_3783_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_dec(v_i_3783_);
return v_entries_3784_;
}
else
{
lean_object* v_k_3787_; lean_object* v_v_3788_; uint64_t v___x_3789_; size_t v_h_3790_; size_t v___x_3791_; lean_object* v___x_3792_; size_t v___x_3793_; size_t v___x_3794_; size_t v___x_3795_; size_t v_h_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_k_3787_ = lean_array_fget_borrowed(v_keys_3781_, v_i_3783_);
v_v_3788_ = lean_array_fget_borrowed(v_vals_3782_, v_i_3783_);
v___x_3789_ = l_Lean_instHashableFVarId_hash(v_k_3787_);
v_h_3790_ = lean_uint64_to_usize(v___x_3789_);
v___x_3791_ = ((size_t)5ULL);
v___x_3792_ = lean_unsigned_to_nat(1u);
v___x_3793_ = ((size_t)1ULL);
v___x_3794_ = lean_usize_sub(v_depth_3780_, v___x_3793_);
v___x_3795_ = lean_usize_mul(v___x_3791_, v___x_3794_);
v_h_3796_ = lean_usize_shift_right(v_h_3790_, v___x_3795_);
v___x_3797_ = lean_nat_add(v_i_3783_, v___x_3792_);
lean_dec(v_i_3783_);
lean_inc(v_v_3788_);
lean_inc(v_k_3787_);
v___x_3798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_entries_3784_, v_h_3796_, v_depth_3780_, v_k_3787_, v_v_3788_);
v_i_3783_ = v___x_3797_;
v_entries_3784_ = v___x_3798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_3800_, lean_object* v_keys_3801_, lean_object* v_vals_3802_, lean_object* v_i_3803_, lean_object* v_entries_3804_){
_start:
{
size_t v_depth_boxed_3805_; lean_object* v_res_3806_; 
v_depth_boxed_3805_ = lean_unbox_usize(v_depth_3800_);
lean_dec(v_depth_3800_);
v_res_3806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_3805_, v_keys_3801_, v_vals_3802_, v_i_3803_, v_entries_3804_);
lean_dec_ref(v_vals_3802_);
lean_dec_ref(v_keys_3801_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_3807_, lean_object* v_x_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
size_t v_x_4265__boxed_3812_; size_t v_x_4266__boxed_3813_; lean_object* v_res_3814_; 
v_x_4265__boxed_3812_ = lean_unbox_usize(v_x_3808_);
lean_dec(v_x_3808_);
v_x_4266__boxed_3813_ = lean_unbox_usize(v_x_3809_);
lean_dec(v_x_3809_);
v_res_3814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3807_, v_x_4265__boxed_3812_, v_x_4266__boxed_3813_, v_x_3810_, v_x_3811_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(lean_object* v_x_3815_, lean_object* v_x_3816_, lean_object* v_x_3817_){
_start:
{
uint64_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3818_ = l_Lean_instHashableFVarId_hash(v_x_3816_);
v___x_3819_ = lean_uint64_to_usize(v___x_3818_);
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3815_, v___x_3819_, v___x_3820_, v_x_3816_, v_x_3817_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f(lean_object* v_fvarId_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
uint8_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = 0;
lean_inc(v_fvarId_3822_);
v___x_3831_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_3822_, v___x_3830_, v_a_3825_, v_a_3827_, v_a_3828_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3906_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3906_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3906_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
if (lean_obj_tag(v_a_3832_) == 1)
{
lean_object* v_val_3836_; lean_object* v___x_3837_; lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3901_; 
lean_del_object(v___x_3834_);
v_val_3836_ = lean_ctor_get(v_a_3832_, 0);
v___x_3837_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_val_3836_, v_a_3824_);
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3901_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3901_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
uint8_t v___x_3842_; 
v___x_3842_ = lean_unbox(v_a_3838_);
lean_dec(v_a_3838_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3896_; 
lean_inc(v_val_3836_);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_a_3832_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v_a_3832_, 0);
lean_dec(v_unused_3897_);
v___x_3844_ = v_a_3832_;
v_isShared_3845_ = v_isSharedCheck_3896_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_a_3832_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3896_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v_letValue_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_st_ref_get(v_a_3824_);
v_letValue_3847_ = lean_ctor_get(v___x_3846_, 4);
lean_inc_ref(v_letValue_3847_);
lean_dec(v___x_3846_);
v___x_3848_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_letValue_3847_, v_fvarId_3822_);
lean_dec_ref(v_letValue_3847_);
if (lean_obj_tag(v___x_3848_) == 1)
{
lean_object* v___x_3850_; 
lean_del_object(v___x_3844_);
lean_dec(v_val_3836_);
lean_dec(v_fvarId_3822_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3848_);
v___x_3850_ = v___x_3840_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
else
{
lean_object* v___x_3852_; 
lean_dec(v___x_3848_);
lean_del_object(v___x_3840_);
v___x_3852_ = l_Lean_Meta_Sym_shareCommon(v_val_3836_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3887_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3887_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3887_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v_share_3858_; lean_object* v_maxFVar_3859_; lean_object* v_proofInstInfo_3860_; lean_object* v_proofInstInfoFVar_3861_; lean_object* v_letValue_3862_; lean_object* v_inferType_3863_; lean_object* v_getLevel_3864_; lean_object* v_congrInfo_3865_; lean_object* v_defEqI_3866_; lean_object* v_extensions_3867_; lean_object* v_issues_3868_; lean_object* v_canon_3869_; lean_object* v_instanceOverrides_3870_; uint8_t v_debug_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3886_; 
v___x_3857_ = lean_st_ref_take(v_a_3824_);
v_share_3858_ = lean_ctor_get(v___x_3857_, 0);
v_maxFVar_3859_ = lean_ctor_get(v___x_3857_, 1);
v_proofInstInfo_3860_ = lean_ctor_get(v___x_3857_, 2);
v_proofInstInfoFVar_3861_ = lean_ctor_get(v___x_3857_, 3);
v_letValue_3862_ = lean_ctor_get(v___x_3857_, 4);
v_inferType_3863_ = lean_ctor_get(v___x_3857_, 5);
v_getLevel_3864_ = lean_ctor_get(v___x_3857_, 6);
v_congrInfo_3865_ = lean_ctor_get(v___x_3857_, 7);
v_defEqI_3866_ = lean_ctor_get(v___x_3857_, 8);
v_extensions_3867_ = lean_ctor_get(v___x_3857_, 9);
v_issues_3868_ = lean_ctor_get(v___x_3857_, 10);
v_canon_3869_ = lean_ctor_get(v___x_3857_, 11);
v_instanceOverrides_3870_ = lean_ctor_get(v___x_3857_, 12);
v_debug_3871_ = lean_ctor_get_uint8(v___x_3857_, sizeof(void*)*13);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3873_ = v___x_3857_;
v_isShared_3874_ = v_isSharedCheck_3886_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_instanceOverrides_3870_);
lean_inc(v_canon_3869_);
lean_inc(v_issues_3868_);
lean_inc(v_extensions_3867_);
lean_inc(v_defEqI_3866_);
lean_inc(v_congrInfo_3865_);
lean_inc(v_getLevel_3864_);
lean_inc(v_inferType_3863_);
lean_inc(v_letValue_3862_);
lean_inc(v_proofInstInfoFVar_3861_);
lean_inc(v_proofInstInfo_3860_);
lean_inc(v_maxFVar_3859_);
lean_inc(v_share_3858_);
lean_dec(v___x_3857_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3886_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_inc(v_a_3853_);
v___x_3875_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(v_letValue_3862_, v_fvarId_3822_, v_a_3853_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 4, v___x_3875_);
v___x_3877_ = v___x_3873_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_share_3858_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_maxFVar_3859_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_proofInstInfo_3860_);
lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_proofInstInfoFVar_3861_);
lean_ctor_set(v_reuseFailAlloc_3885_, 4, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3885_, 5, v_inferType_3863_);
lean_ctor_set(v_reuseFailAlloc_3885_, 6, v_getLevel_3864_);
lean_ctor_set(v_reuseFailAlloc_3885_, 7, v_congrInfo_3865_);
lean_ctor_set(v_reuseFailAlloc_3885_, 8, v_defEqI_3866_);
lean_ctor_set(v_reuseFailAlloc_3885_, 9, v_extensions_3867_);
lean_ctor_set(v_reuseFailAlloc_3885_, 10, v_issues_3868_);
lean_ctor_set(v_reuseFailAlloc_3885_, 11, v_canon_3869_);
lean_ctor_set(v_reuseFailAlloc_3885_, 12, v_instanceOverrides_3870_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*13, v_debug_3871_);
v___x_3877_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3878_ = lean_st_ref_put(v_a_3824_, v___x_3877_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v_a_3853_);
v___x_3880_ = v___x_3844_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3853_);
v___x_3880_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3882_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3880_);
v___x_3882_ = v___x_3855_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_del_object(v___x_3844_);
lean_dec(v_fvarId_3822_);
v_a_3888_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3852_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3852_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
}
else
{
lean_object* v___x_3899_; 
lean_dec(v_fvarId_3822_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_a_3832_);
v___x_3899_ = v___x_3840_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3832_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
lean_dec(v_a_3832_);
lean_dec(v_fvarId_3822_);
v___x_3902_ = lean_box(0);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3902_);
v___x_3904_ = v___x_3834_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_dec(v_fvarId_3822_);
return v___x_3831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f___boxed(lean_object* v_fvarId_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Meta_Sym_getLetValueS_x3f(v_fvarId_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(lean_object* v_00_u03b2_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_x_3917_, v_x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___boxed(lean_object* v_00_u03b2_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(v_00_u03b2_3920_, v_x_3921_, v_x_3922_);
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3921_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1(lean_object* v_00_u03b2_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_, lean_object* v_x_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(v_x_3925_, v_x_3926_, v_x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3929_, lean_object* v_x_3930_, size_t v_x_3931_, lean_object* v_x_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3930_, v_x_3931_, v_x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3934_, lean_object* v_x_3935_, lean_object* v_x_3936_, lean_object* v_x_3937_){
_start:
{
size_t v_x_4577__boxed_3938_; lean_object* v_res_3939_; 
v_x_4577__boxed_3938_ = lean_unbox_usize(v_x_3936_);
lean_dec(v_x_3936_);
v_res_3939_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(v_00_u03b2_3934_, v_x_3935_, v_x_4577__boxed_3938_, v_x_3937_);
lean_dec(v_x_3937_);
lean_dec_ref(v_x_3935_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(lean_object* v_00_u03b2_3940_, lean_object* v_x_3941_, size_t v_x_3942_, size_t v_x_3943_, lean_object* v_x_3944_, lean_object* v_x_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3941_, v_x_3942_, v_x_3943_, v_x_3944_, v_x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3947_, lean_object* v_x_3948_, lean_object* v_x_3949_, lean_object* v_x_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_){
_start:
{
size_t v_x_4588__boxed_3953_; size_t v_x_4589__boxed_3954_; lean_object* v_res_3955_; 
v_x_4588__boxed_3953_ = lean_unbox_usize(v_x_3949_);
lean_dec(v_x_3949_);
v_x_4589__boxed_3954_ = lean_unbox_usize(v_x_3950_);
lean_dec(v_x_3950_);
v_res_3955_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(v_00_u03b2_3947_, v_x_3948_, v_x_4588__boxed_3953_, v_x_4589__boxed_3954_, v_x_3951_, v_x_3952_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3956_, lean_object* v_keys_3957_, lean_object* v_vals_3958_, lean_object* v_heq_3959_, lean_object* v_i_3960_, lean_object* v_k_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3957_, v_vals_3958_, v_i_3960_, v_k_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3963_, lean_object* v_keys_3964_, lean_object* v_vals_3965_, lean_object* v_heq_3966_, lean_object* v_i_3967_, lean_object* v_k_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3963_, v_keys_3964_, v_vals_3965_, v_heq_3966_, v_i_3967_, v_k_3968_);
lean_dec(v_k_3968_);
lean_dec_ref(v_vals_3965_);
lean_dec_ref(v_keys_3964_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3970_, lean_object* v_n_3971_, lean_object* v_k_3972_, lean_object* v_v_3973_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(v_n_3971_, v_k_3972_, v_v_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3975_, size_t v_depth_3976_, lean_object* v_keys_3977_, lean_object* v_vals_3978_, lean_object* v_heq_3979_, lean_object* v_i_3980_, lean_object* v_entries_3981_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_depth_3976_, v_keys_3977_, v_vals_3978_, v_i_3980_, v_entries_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3983_, lean_object* v_depth_3984_, lean_object* v_keys_3985_, lean_object* v_vals_3986_, lean_object* v_heq_3987_, lean_object* v_i_3988_, lean_object* v_entries_3989_){
_start:
{
size_t v_depth_boxed_3990_; lean_object* v_res_3991_; 
v_depth_boxed_3990_ = lean_unbox_usize(v_depth_3984_);
lean_dec(v_depth_3984_);
v_res_3991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(v_00_u03b2_3983_, v_depth_boxed_3990_, v_keys_3985_, v_vals_3986_, v_heq_3987_, v_i_3988_, v_entries_3989_);
lean_dec_ref(v_vals_3986_);
lean_dec_ref(v_keys_3985_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3992_, lean_object* v_x_3993_, lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3993_, v_x_3994_, v_x_3995_, v_x_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_Meta_Sym_share(v_e_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_4016_){
_start:
{
lean_object* v___x_4018_; uint8_t v_debug_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4018_ = lean_st_ref_get(v_a_4016_);
v_debug_4019_ = lean_ctor_get_uint8(v___x_4018_, sizeof(void*)*13);
lean_dec(v___x_4018_);
v___x_4020_ = lean_box(v_debug_4019_);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_4022_);
lean_dec(v_a_4022_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___x_4032_; uint8_t v_debug_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4032_ = lean_st_ref_get(v_a_4026_);
v_debug_4033_ = lean_ctor_get_uint8(v___x_4032_, sizeof(void*)*13);
lean_dec(v___x_4032_);
v___x_4034_ = lean_box(v_debug_4033_);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_4044_){
_start:
{
lean_object* v_config_4046_; lean_object* v___x_4047_; 
v_config_4046_ = lean_ctor_get(v_a_4044_, 1);
lean_inc_ref(v_config_4046_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v_config_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4048_);
lean_dec_ref(v_a_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4051_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Meta_Sym_getConfig(v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_4067_, lean_object* v_msg_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v_ref_4074_; lean_object* v___x_4075_; lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4121_; 
v_ref_4074_ = lean_ctor_get(v___y_4071_, 2);
v___x_4075_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4121_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4121_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; lean_object* v_traceState_4081_; lean_object* v_env_4082_; lean_object* v_nextMacroScope_4083_; lean_object* v_ngen_4084_; lean_object* v_auxDeclNGen_4085_; lean_object* v_cache_4086_; lean_object* v_recordedDeps_4087_; lean_object* v_messages_4088_; lean_object* v_infoState_4089_; lean_object* v_snapshotTasks_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4120_; 
v___x_4080_ = lean_st_ref_take(v___y_4072_);
v_traceState_4081_ = lean_ctor_get(v___x_4080_, 4);
v_env_4082_ = lean_ctor_get(v___x_4080_, 0);
v_nextMacroScope_4083_ = lean_ctor_get(v___x_4080_, 1);
v_ngen_4084_ = lean_ctor_get(v___x_4080_, 2);
v_auxDeclNGen_4085_ = lean_ctor_get(v___x_4080_, 3);
v_cache_4086_ = lean_ctor_get(v___x_4080_, 5);
v_recordedDeps_4087_ = lean_ctor_get(v___x_4080_, 6);
v_messages_4088_ = lean_ctor_get(v___x_4080_, 7);
v_infoState_4089_ = lean_ctor_get(v___x_4080_, 8);
v_snapshotTasks_4090_ = lean_ctor_get(v___x_4080_, 9);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4092_ = v___x_4080_;
v_isShared_4093_ = v_isSharedCheck_4120_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_snapshotTasks_4090_);
lean_inc(v_infoState_4089_);
lean_inc(v_messages_4088_);
lean_inc(v_recordedDeps_4087_);
lean_inc(v_cache_4086_);
lean_inc(v_traceState_4081_);
lean_inc(v_auxDeclNGen_4085_);
lean_inc(v_ngen_4084_);
lean_inc(v_nextMacroScope_4083_);
lean_inc(v_env_4082_);
lean_dec(v___x_4080_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4120_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
uint64_t v_tid_4094_; lean_object* v_traces_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4119_; 
v_tid_4094_ = lean_ctor_get_uint64(v_traceState_4081_, sizeof(void*)*1);
v_traces_4095_ = lean_ctor_get(v_traceState_4081_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_traceState_4081_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4097_ = v_traceState_4081_;
v_isShared_4098_ = v_isSharedCheck_4119_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_traces_4095_);
lean_dec(v_traceState_4081_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4119_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; double v___x_4101_; uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4099_ = lean_box(0);
v___x_4100_ = lean_box(0);
v___x_4101_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_4102_ = 0;
v___x_4103_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4104_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4104_, 0, v_cls_4067_);
lean_ctor_set(v___x_4104_, 1, v___x_4100_);
lean_ctor_set(v___x_4104_, 2, v___x_4103_);
lean_ctor_set_float(v___x_4104_, sizeof(void*)*3, v___x_4101_);
lean_ctor_set_float(v___x_4104_, sizeof(void*)*3 + 8, v___x_4101_);
lean_ctor_set_uint8(v___x_4104_, sizeof(void*)*3 + 16, v___x_4102_);
v___x_4105_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_4106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v_a_4076_);
lean_ctor_set(v___x_4106_, 2, v___x_4105_);
lean_inc(v_ref_4074_);
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v_ref_4074_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_PersistentArray_push___redArg(v_traces_4095_, v___x_4107_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4108_);
v___x_4110_ = v___x_4097_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4108_);
lean_ctor_set_uint64(v_reuseFailAlloc_4118_, sizeof(void*)*1, v_tid_4094_);
v___x_4110_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4112_; 
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 4, v___x_4110_);
v___x_4112_ = v___x_4092_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_env_4082_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v_nextMacroScope_4083_);
lean_ctor_set(v_reuseFailAlloc_4117_, 2, v_ngen_4084_);
lean_ctor_set(v_reuseFailAlloc_4117_, 3, v_auxDeclNGen_4085_);
lean_ctor_set(v_reuseFailAlloc_4117_, 4, v___x_4110_);
lean_ctor_set(v_reuseFailAlloc_4117_, 5, v_cache_4086_);
lean_ctor_set(v_reuseFailAlloc_4117_, 6, v_recordedDeps_4087_);
lean_ctor_set(v_reuseFailAlloc_4117_, 7, v_messages_4088_);
lean_ctor_set(v_reuseFailAlloc_4117_, 8, v_infoState_4089_);
lean_ctor_set(v_reuseFailAlloc_4117_, 9, v_snapshotTasks_4090_);
v___x_4112_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4113_ = lean_st_ref_put(v___y_4072_, v___x_4112_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 0, v___x_4099_);
v___x_4115_ = v___x_4078_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4099_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_4122_, lean_object* v_msg_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_4122_, v_msg_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4129_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_4133_; uint8_t v___x_4134_; double v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4133_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4134_ = 1;
v___x_4135_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_4136_ = lean_box(0);
v___x_4137_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_4138_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v___x_4136_);
lean_ctor_set(v___x_4138_, 2, v___x_4133_);
lean_ctor_set_float(v___x_4138_, sizeof(void*)*3, v___x_4135_);
lean_ctor_set_float(v___x_4138_, sizeof(void*)*3 + 8, v___x_4135_);
lean_ctor_set_uint8(v___x_4138_, sizeof(void*)*3 + 16, v___x_4134_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4150_; lean_object* v_a_4151_; lean_object* v___x_4152_; lean_object* v_share_4153_; lean_object* v_maxFVar_4154_; lean_object* v_proofInstInfo_4155_; lean_object* v_proofInstInfoFVar_4156_; lean_object* v_letValue_4157_; lean_object* v_inferType_4158_; lean_object* v_getLevel_4159_; lean_object* v_congrInfo_4160_; lean_object* v_defEqI_4161_; lean_object* v_extensions_4162_; lean_object* v_issues_4163_; lean_object* v_canon_4164_; lean_object* v_instanceOverrides_4165_; uint8_t v_debug_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4186_; 
v___x_4150_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_4139_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref(v___x_4150_);
v___x_4152_ = lean_st_ref_take(v_a_4141_);
v_share_4153_ = lean_ctor_get(v___x_4152_, 0);
v_maxFVar_4154_ = lean_ctor_get(v___x_4152_, 1);
v_proofInstInfo_4155_ = lean_ctor_get(v___x_4152_, 2);
v_proofInstInfoFVar_4156_ = lean_ctor_get(v___x_4152_, 3);
v_letValue_4157_ = lean_ctor_get(v___x_4152_, 4);
v_inferType_4158_ = lean_ctor_get(v___x_4152_, 5);
v_getLevel_4159_ = lean_ctor_get(v___x_4152_, 6);
v_congrInfo_4160_ = lean_ctor_get(v___x_4152_, 7);
v_defEqI_4161_ = lean_ctor_get(v___x_4152_, 8);
v_extensions_4162_ = lean_ctor_get(v___x_4152_, 9);
v_issues_4163_ = lean_ctor_get(v___x_4152_, 10);
v_canon_4164_ = lean_ctor_get(v___x_4152_, 11);
v_instanceOverrides_4165_ = lean_ctor_get(v___x_4152_, 12);
v_debug_4166_ = lean_ctor_get_uint8(v___x_4152_, sizeof(void*)*13);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4168_ = v___x_4152_;
v_isShared_4169_ = v_isSharedCheck_4186_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_instanceOverrides_4165_);
lean_inc(v_canon_4164_);
lean_inc(v_issues_4163_);
lean_inc(v_extensions_4162_);
lean_inc(v_defEqI_4161_);
lean_inc(v_congrInfo_4160_);
lean_inc(v_getLevel_4159_);
lean_inc(v_inferType_4158_);
lean_inc(v_letValue_4157_);
lean_inc(v_proofInstInfoFVar_4156_);
lean_inc(v_proofInstInfo_4155_);
lean_inc(v_maxFVar_4154_);
lean_inc(v_share_4153_);
lean_dec(v___x_4152_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4186_;
goto v_resetjp_4167_;
}
v___jp_4147_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_box(0);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4170_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_4171_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_4151_);
v___x_4172_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4170_);
lean_ctor_set(v___x_4172_, 1, v_a_4151_);
lean_ctor_set(v___x_4172_, 2, v___x_4171_);
v___x_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set(v___x_4173_, 1, v_issues_4163_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 10, v___x_4173_);
v___x_4175_ = v___x_4168_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_share_4153_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v_maxFVar_4154_);
lean_ctor_set(v_reuseFailAlloc_4185_, 2, v_proofInstInfo_4155_);
lean_ctor_set(v_reuseFailAlloc_4185_, 3, v_proofInstInfoFVar_4156_);
lean_ctor_set(v_reuseFailAlloc_4185_, 4, v_letValue_4157_);
lean_ctor_set(v_reuseFailAlloc_4185_, 5, v_inferType_4158_);
lean_ctor_set(v_reuseFailAlloc_4185_, 6, v_getLevel_4159_);
lean_ctor_set(v_reuseFailAlloc_4185_, 7, v_congrInfo_4160_);
lean_ctor_set(v_reuseFailAlloc_4185_, 8, v_defEqI_4161_);
lean_ctor_set(v_reuseFailAlloc_4185_, 9, v_extensions_4162_);
lean_ctor_set(v_reuseFailAlloc_4185_, 10, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4185_, 11, v_canon_4164_);
lean_ctor_set(v_reuseFailAlloc_4185_, 12, v_instanceOverrides_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4185_, sizeof(void*)*13, v_debug_4166_);
v___x_4175_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4176_; lean_object* v_toCold_4177_; lean_object* v_options_4178_; uint8_t v_hasTrace_4179_; 
v___x_4176_ = lean_st_ref_put(v_a_4141_, v___x_4175_);
v_toCold_4177_ = lean_ctor_get(v_a_4144_, 0);
v_options_4178_ = lean_ctor_get(v_toCold_4177_, 2);
v_hasTrace_4179_ = lean_ctor_get_uint8(v_options_4178_, sizeof(void*)*1);
if (v_hasTrace_4179_ == 0)
{
lean_dec(v_a_4151_);
goto v___jp_4147_;
}
else
{
lean_object* v_inheritedTraceOptions_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v_inheritedTraceOptions_4180_ = lean_ctor_get(v_toCold_4177_, 11);
v___x_4181_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_4182_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_4183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4180_, v_options_4178_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_dec(v_a_4151_);
goto v___jp_4147_;
}
else
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_4181_, v_a_4151_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
return v___x_4184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Meta_Sym_reportIssue(v_msg_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_4196_, lean_object* v_msg_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_4196_, v_msg_4197_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_4206_, lean_object* v_msg_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_4206_, v_msg_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v___x_4224_; lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4235_; 
v___x_4224_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4217_);
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4235_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4235_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
uint8_t v_verbose_4229_; 
v_verbose_4229_ = lean_ctor_get_uint8(v_a_4225_, 0);
lean_dec(v_a_4225_);
if (v_verbose_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4232_; 
lean_dec_ref(v_msg_4216_);
v___x_4230_ = lean_box(0);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4230_);
v___x_4232_ = v___x_4227_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4230_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
else
{
lean_object* v___x_4234_; 
lean_del_object(v___x_4227_);
v___x_4234_ = l_Lean_Meta_Sym_reportIssue(v_msg_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
return v___x_4234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
return v_res_4244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_4261_ = l_String_toRawSubstring_x27(v___x_4260_);
return v___x_4261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4300_ = l_String_toRawSubstring_x27(v___x_4299_);
return v___x_4300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_4313_ = l_String_toRawSubstring_x27(v___x_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v_msg_4340_; lean_object* v_quotContext_4341_; lean_object* v_currMacroScope_4342_; lean_object* v_ref_4343_; lean_object* v___y_4344_; lean_object* v___x_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; 
lean_inc(v_s_4336_);
v___x_4359_ = l_Lean_Syntax_getKind(v_s_4336_);
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4361_ = lean_name_eq(v___x_4359_, v___x_4360_);
lean_dec(v___x_4359_);
if (v___x_4361_ == 0)
{
lean_object* v_quotContext_4362_; lean_object* v_currMacroScope_4363_; lean_object* v_ref_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v_quotContext_4362_ = lean_ctor_get(v_a_4337_, 1);
v_currMacroScope_4363_ = lean_ctor_get(v_a_4337_, 2);
v_ref_4364_ = lean_ctor_get(v_a_4337_, 5);
v___x_4365_ = l_Lean_SourceInfo_fromRef(v_ref_4364_, v___x_4361_);
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4367_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4368_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4365_, 8);
v___x_4369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4365_);
lean_ctor_set(v___x_4369_, 1, v___x_4368_);
v___x_4370_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4371_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4372_ = lean_box(0);
lean_inc_n(v_currMacroScope_4363_, 3);
lean_inc_n(v_quotContext_4362_, 3);
v___x_4373_ = l_Lean_addMacroScope(v_quotContext_4362_, v___x_4372_, v_currMacroScope_4363_);
v___x_4374_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4375_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4365_);
lean_ctor_set(v___x_4375_, 1, v___x_4371_);
lean_ctor_set(v___x_4375_, 2, v___x_4373_);
lean_ctor_set(v___x_4375_, 3, v___x_4374_);
v___x_4376_ = l_Lean_Syntax_node1(v___x_4365_, v___x_4370_, v___x_4375_);
v___x_4377_ = l_Lean_Syntax_node2(v___x_4365_, v___x_4367_, v___x_4369_, v___x_4376_);
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4365_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4381_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4382_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4383_ = l_Lean_addMacroScope(v_quotContext_4362_, v___x_4382_, v_currMacroScope_4363_);
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4385_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4365_);
lean_ctor_set(v___x_4385_, 1, v___x_4381_);
lean_ctor_set(v___x_4385_, 2, v___x_4383_);
lean_ctor_set(v___x_4385_, 3, v___x_4384_);
v___x_4386_ = l_Lean_Syntax_node1(v___x_4365_, v___x_4380_, v___x_4385_);
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4365_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = l_Lean_Syntax_node5(v___x_4365_, v___x_4366_, v___x_4377_, v_s_4336_, v___x_4379_, v___x_4386_, v___x_4388_);
v_msg_4340_ = v___x_4389_;
v_quotContext_4341_ = v_quotContext_4362_;
v_currMacroScope_4342_ = v_currMacroScope_4363_;
v_ref_4343_ = v_ref_4364_;
v___y_4344_ = v_a_4338_;
goto v___jp_4339_;
}
else
{
lean_object* v_quotContext_4390_; lean_object* v_currMacroScope_4391_; lean_object* v_ref_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_quotContext_4390_ = lean_ctor_get(v_a_4337_, 1);
v_currMacroScope_4391_ = lean_ctor_get(v_a_4337_, 2);
v_ref_4392_ = lean_ctor_get(v_a_4337_, 5);
v___x_4393_ = 0;
v___x_4394_ = l_Lean_SourceInfo_fromRef(v_ref_4392_, v___x_4393_);
v___x_4395_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4396_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4394_);
v___x_4397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4394_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = l_Lean_Syntax_node2(v___x_4394_, v___x_4395_, v___x_4397_, v_s_4336_);
lean_inc(v_currMacroScope_4391_);
lean_inc(v_quotContext_4390_);
v_msg_4340_ = v___x_4398_;
v_quotContext_4341_ = v_quotContext_4390_;
v_currMacroScope_4342_ = v_currMacroScope_4391_;
v_ref_4343_ = v_ref_4392_;
v___y_4344_ = v_a_4338_;
goto v___jp_4339_;
}
v___jp_4339_:
{
uint8_t v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4345_ = 0;
v___x_4346_ = l_Lean_SourceInfo_fromRef(v_ref_4343_, v___x_4345_);
v___x_4347_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4348_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4349_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_4351_ = l_Lean_addMacroScope(v_quotContext_4341_, v___x_4350_, v_currMacroScope_4342_);
v___x_4352_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_4346_, 3);
v___x_4353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4346_);
lean_ctor_set(v___x_4353_, 1, v___x_4349_);
lean_ctor_set(v___x_4353_, 2, v___x_4351_);
lean_ctor_set(v___x_4353_, 3, v___x_4352_);
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4355_ = l_Lean_Syntax_node1(v___x_4346_, v___x_4354_, v_msg_4340_);
v___x_4356_ = l_Lean_Syntax_node2(v___x_4346_, v___x_4348_, v___x_4353_, v___x_4355_);
v___x_4357_ = l_Lean_Syntax_node1(v___x_4346_, v___x_4347_, v___x_4356_);
v___x_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
lean_ctor_set(v___x_4358_, 1, v___y_4344_);
return v___x_4358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_4399_, v_a_4400_, v_a_4401_);
lean_dec_ref(v_a_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4446_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_4443_);
v___x_4447_ = l_Lean_Syntax_isOfKind(v_x_4443_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec(v_x_4443_);
v___x_4448_ = lean_box(1);
v___x_4449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
lean_ctor_set(v___x_4449_, 1, v_a_4445_);
return v___x_4449_;
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v_a_4453_; lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
v___x_4450_ = lean_unsigned_to_nat(1u);
v___x_4451_ = l_Lean_Syntax_getArg(v_x_4443_, v___x_4450_);
lean_dec(v_x_4443_);
v___x_4452_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_4451_, v_a_4444_, v_a_4445_);
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
v_a_4454_ = lean_ctor_get(v___x_4452_, 1);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4452_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_inc(v_a_4453_);
lean_dec(v___x_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4453_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4462_, v_a_4463_, v_a_4464_);
lean_dec_ref(v_a_4463_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4494_; 
v___x_4474_ = l_Lean_KVMap_instValueBool;
v___x_4475_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4467_);
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4478_ = v___x_4475_;
v_isShared_4479_ = v_isSharedCheck_4494_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4475_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4494_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
uint8_t v_verbose_4480_; 
v_verbose_4480_ = lean_ctor_get_uint8(v_a_4476_, 0);
lean_dec(v_a_4476_);
if (v_verbose_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4483_; 
lean_dec_ref(v_msg_4466_);
v___x_4481_ = lean_box(0);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v___x_4481_);
v___x_4483_ = v___x_4478_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4485_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4471_);
v___x_4486_ = l_Lean_Meta_Sym_sym_debug;
v___x_4487_ = l_Lean_Option_get___redArg(v___x_4474_, v___x_4485_, v___x_4486_);
lean_dec_ref(v___x_4485_);
v___x_4488_ = lean_unbox(v___x_4487_);
lean_dec(v___x_4487_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; lean_object* v___x_4491_; 
lean_dec_ref(v_msg_4466_);
v___x_4489_ = lean_box(0);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v___x_4489_);
v___x_4491_ = v___x_4478_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
else
{
lean_object* v___x_4493_; 
lean_del_object(v___x_4478_);
v___x_4493_ = l_Lean_Meta_Sym_reportIssue(v_msg_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
return v___x_4493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
return v_res_4503_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4506_ = l_String_toRawSubstring_x27(v___x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_msg_4526_; lean_object* v_quotContext_4527_; lean_object* v_currMacroScope_4528_; lean_object* v_ref_4529_; lean_object* v___y_4530_; lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; 
lean_inc(v_s_4522_);
v___x_4545_ = l_Lean_Syntax_getKind(v_s_4522_);
v___x_4546_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4547_ = lean_name_eq(v___x_4545_, v___x_4546_);
lean_dec(v___x_4545_);
if (v___x_4547_ == 0)
{
lean_object* v_quotContext_4548_; lean_object* v_currMacroScope_4549_; lean_object* v_ref_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_quotContext_4548_ = lean_ctor_get(v_a_4523_, 1);
v_currMacroScope_4549_ = lean_ctor_get(v_a_4523_, 2);
v_ref_4550_ = lean_ctor_get(v_a_4523_, 5);
v___x_4551_ = l_Lean_SourceInfo_fromRef(v_ref_4550_, v___x_4547_);
v___x_4552_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4553_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4554_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4551_, 8);
v___x_4555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4551_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4557_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4558_ = lean_box(0);
lean_inc_n(v_currMacroScope_4549_, 3);
lean_inc_n(v_quotContext_4548_, 3);
v___x_4559_ = l_Lean_addMacroScope(v_quotContext_4548_, v___x_4558_, v_currMacroScope_4549_);
v___x_4560_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4561_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4551_);
lean_ctor_set(v___x_4561_, 1, v___x_4557_);
lean_ctor_set(v___x_4561_, 2, v___x_4559_);
lean_ctor_set(v___x_4561_, 3, v___x_4560_);
v___x_4562_ = l_Lean_Syntax_node1(v___x_4551_, v___x_4556_, v___x_4561_);
v___x_4563_ = l_Lean_Syntax_node2(v___x_4551_, v___x_4553_, v___x_4555_, v___x_4562_);
v___x_4564_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4551_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4567_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4568_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4569_ = l_Lean_addMacroScope(v_quotContext_4548_, v___x_4568_, v_currMacroScope_4549_);
v___x_4570_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4551_);
lean_ctor_set(v___x_4571_, 1, v___x_4567_);
lean_ctor_set(v___x_4571_, 2, v___x_4569_);
lean_ctor_set(v___x_4571_, 3, v___x_4570_);
v___x_4572_ = l_Lean_Syntax_node1(v___x_4551_, v___x_4566_, v___x_4571_);
v___x_4573_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4551_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
v___x_4575_ = l_Lean_Syntax_node5(v___x_4551_, v___x_4552_, v___x_4563_, v_s_4522_, v___x_4565_, v___x_4572_, v___x_4574_);
v_msg_4526_ = v___x_4575_;
v_quotContext_4527_ = v_quotContext_4548_;
v_currMacroScope_4528_ = v_currMacroScope_4549_;
v_ref_4529_ = v_ref_4550_;
v___y_4530_ = v_a_4524_;
goto v___jp_4525_;
}
else
{
lean_object* v_quotContext_4576_; lean_object* v_currMacroScope_4577_; lean_object* v_ref_4578_; uint8_t v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v_quotContext_4576_ = lean_ctor_get(v_a_4523_, 1);
v_currMacroScope_4577_ = lean_ctor_get(v_a_4523_, 2);
v_ref_4578_ = lean_ctor_get(v_a_4523_, 5);
v___x_4579_ = 0;
v___x_4580_ = l_Lean_SourceInfo_fromRef(v_ref_4578_, v___x_4579_);
v___x_4581_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4582_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4580_);
v___x_4583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4580_);
lean_ctor_set(v___x_4583_, 1, v___x_4582_);
v___x_4584_ = l_Lean_Syntax_node2(v___x_4580_, v___x_4581_, v___x_4583_, v_s_4522_);
lean_inc(v_currMacroScope_4577_);
lean_inc(v_quotContext_4576_);
v_msg_4526_ = v___x_4584_;
v_quotContext_4527_ = v_quotContext_4576_;
v_currMacroScope_4528_ = v_currMacroScope_4577_;
v_ref_4529_ = v_ref_4578_;
v___y_4530_ = v_a_4524_;
goto v___jp_4525_;
}
v___jp_4525_:
{
uint8_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4531_ = 0;
v___x_4532_ = l_Lean_SourceInfo_fromRef(v_ref_4529_, v___x_4531_);
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4534_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4535_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4536_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4537_ = l_Lean_addMacroScope(v_quotContext_4527_, v___x_4536_, v_currMacroScope_4528_);
v___x_4538_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4532_, 3);
v___x_4539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4532_);
lean_ctor_set(v___x_4539_, 1, v___x_4535_);
lean_ctor_set(v___x_4539_, 2, v___x_4537_);
lean_ctor_set(v___x_4539_, 3, v___x_4538_);
v___x_4540_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4541_ = l_Lean_Syntax_node1(v___x_4532_, v___x_4540_, v_msg_4526_);
v___x_4542_ = l_Lean_Syntax_node2(v___x_4532_, v___x_4534_, v___x_4539_, v___x_4541_);
v___x_4543_ = l_Lean_Syntax_node1(v___x_4532_, v___x_4533_, v___x_4542_);
v___x_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
lean_ctor_set(v___x_4544_, 1, v___y_4530_);
return v___x_4544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4585_, v_a_4586_, v_a_4587_);
lean_dec_ref(v_a_4586_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v___x_4610_; uint8_t v___x_4611_; 
v___x_4610_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4607_);
v___x_4611_ = l_Lean_Syntax_isOfKind(v_x_4607_, v___x_4610_);
if (v___x_4611_ == 0)
{
lean_object* v___x_4612_; lean_object* v___x_4613_; 
lean_dec(v_x_4607_);
v___x_4612_ = lean_box(1);
v___x_4613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4612_);
lean_ctor_set(v___x_4613_, 1, v_a_4609_);
return v___x_4613_;
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v_a_4617_; lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
v___x_4614_ = lean_unsigned_to_nat(1u);
v___x_4615_ = l_Lean_Syntax_getArg(v_x_4607_, v___x_4614_);
lean_dec(v_x_4607_);
v___x_4616_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4615_, v_a_4608_, v_a_4609_);
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_a_4618_ = lean_ctor_get(v___x_4616_, 1);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4616_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4617_);
lean_ctor_set(v_reuseFailAlloc_4624_, 1, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4626_, v_a_4627_, v_a_4628_);
lean_dec_ref(v_a_4627_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4630_){
_start:
{
lean_object* v___x_4632_; lean_object* v_issues_4633_; lean_object* v___x_4634_; 
v___x_4632_ = lean_st_ref_get(v_a_4630_);
v_issues_4633_ = lean_ctor_get(v___x_4632_, 10);
lean_inc(v_issues_4633_);
lean_dec(v___x_4632_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_issues_4633_);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4635_);
lean_dec(v_a_4635_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4639_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Meta_Sym_getIssues(v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4654_, lean_object* v_issues_4655_, lean_object* v_a_x3f_4656_){
_start:
{
lean_object* v___x_4658_; lean_object* v_share_4659_; lean_object* v_maxFVar_4660_; lean_object* v_proofInstInfo_4661_; lean_object* v_proofInstInfoFVar_4662_; lean_object* v_letValue_4663_; lean_object* v_inferType_4664_; lean_object* v_getLevel_4665_; lean_object* v_congrInfo_4666_; lean_object* v_defEqI_4667_; lean_object* v_extensions_4668_; lean_object* v_issues_4669_; lean_object* v_canon_4670_; lean_object* v_instanceOverrides_4671_; uint8_t v_debug_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4683_; 
v___x_4658_ = lean_st_ref_take(v_a_4654_);
v_share_4659_ = lean_ctor_get(v___x_4658_, 0);
v_maxFVar_4660_ = lean_ctor_get(v___x_4658_, 1);
v_proofInstInfo_4661_ = lean_ctor_get(v___x_4658_, 2);
v_proofInstInfoFVar_4662_ = lean_ctor_get(v___x_4658_, 3);
v_letValue_4663_ = lean_ctor_get(v___x_4658_, 4);
v_inferType_4664_ = lean_ctor_get(v___x_4658_, 5);
v_getLevel_4665_ = lean_ctor_get(v___x_4658_, 6);
v_congrInfo_4666_ = lean_ctor_get(v___x_4658_, 7);
v_defEqI_4667_ = lean_ctor_get(v___x_4658_, 8);
v_extensions_4668_ = lean_ctor_get(v___x_4658_, 9);
v_issues_4669_ = lean_ctor_get(v___x_4658_, 10);
v_canon_4670_ = lean_ctor_get(v___x_4658_, 11);
v_instanceOverrides_4671_ = lean_ctor_get(v___x_4658_, 12);
v_debug_4672_ = lean_ctor_get_uint8(v___x_4658_, sizeof(void*)*13);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4674_ = v___x_4658_;
v_isShared_4675_ = v_isSharedCheck_4683_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_instanceOverrides_4671_);
lean_inc(v_canon_4670_);
lean_inc(v_issues_4669_);
lean_inc(v_extensions_4668_);
lean_inc(v_defEqI_4667_);
lean_inc(v_congrInfo_4666_);
lean_inc(v_getLevel_4665_);
lean_inc(v_inferType_4664_);
lean_inc(v_letValue_4663_);
lean_inc(v_proofInstInfoFVar_4662_);
lean_inc(v_proofInstInfo_4661_);
lean_inc(v_maxFVar_4660_);
lean_inc(v_share_4659_);
lean_dec(v___x_4658_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4683_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v___x_4676_ = lean_box(0);
v___x_4677_ = l_List_appendTR___redArg(v_issues_4669_, v_issues_4655_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 10, v___x_4677_);
v___x_4679_ = v___x_4674_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_share_4659_);
lean_ctor_set(v_reuseFailAlloc_4682_, 1, v_maxFVar_4660_);
lean_ctor_set(v_reuseFailAlloc_4682_, 2, v_proofInstInfo_4661_);
lean_ctor_set(v_reuseFailAlloc_4682_, 3, v_proofInstInfoFVar_4662_);
lean_ctor_set(v_reuseFailAlloc_4682_, 4, v_letValue_4663_);
lean_ctor_set(v_reuseFailAlloc_4682_, 5, v_inferType_4664_);
lean_ctor_set(v_reuseFailAlloc_4682_, 6, v_getLevel_4665_);
lean_ctor_set(v_reuseFailAlloc_4682_, 7, v_congrInfo_4666_);
lean_ctor_set(v_reuseFailAlloc_4682_, 8, v_defEqI_4667_);
lean_ctor_set(v_reuseFailAlloc_4682_, 9, v_extensions_4668_);
lean_ctor_set(v_reuseFailAlloc_4682_, 10, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4682_, 11, v_canon_4670_);
lean_ctor_set(v_reuseFailAlloc_4682_, 12, v_instanceOverrides_4671_);
lean_ctor_set_uint8(v_reuseFailAlloc_4682_, sizeof(void*)*13, v_debug_4672_);
v___x_4679_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = lean_st_ref_put(v_a_4654_, v___x_4679_);
v___x_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4676_);
return v___x_4681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4684_, lean_object* v_issues_4685_, lean_object* v_a_x3f_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4684_, v_issues_4685_, v_a_x3f_4686_);
lean_dec(v_a_x3f_4686_);
lean_dec(v_a_4684_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v___x_4697_; lean_object* v_issues_4698_; lean_object* v___x_4699_; lean_object* v_share_4700_; lean_object* v_maxFVar_4701_; lean_object* v_proofInstInfo_4702_; lean_object* v_proofInstInfoFVar_4703_; lean_object* v_letValue_4704_; lean_object* v_inferType_4705_; lean_object* v_getLevel_4706_; lean_object* v_congrInfo_4707_; lean_object* v_defEqI_4708_; lean_object* v_extensions_4709_; lean_object* v_canon_4710_; lean_object* v_instanceOverrides_4711_; uint8_t v_debug_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4750_; 
v___x_4697_ = lean_st_ref_get(v_a_4691_);
v_issues_4698_ = lean_ctor_get(v___x_4697_, 10);
lean_inc(v_issues_4698_);
lean_dec(v___x_4697_);
v___x_4699_ = lean_st_ref_take(v_a_4691_);
v_share_4700_ = lean_ctor_get(v___x_4699_, 0);
v_maxFVar_4701_ = lean_ctor_get(v___x_4699_, 1);
v_proofInstInfo_4702_ = lean_ctor_get(v___x_4699_, 2);
v_proofInstInfoFVar_4703_ = lean_ctor_get(v___x_4699_, 3);
v_letValue_4704_ = lean_ctor_get(v___x_4699_, 4);
v_inferType_4705_ = lean_ctor_get(v___x_4699_, 5);
v_getLevel_4706_ = lean_ctor_get(v___x_4699_, 6);
v_congrInfo_4707_ = lean_ctor_get(v___x_4699_, 7);
v_defEqI_4708_ = lean_ctor_get(v___x_4699_, 8);
v_extensions_4709_ = lean_ctor_get(v___x_4699_, 9);
v_canon_4710_ = lean_ctor_get(v___x_4699_, 11);
v_instanceOverrides_4711_ = lean_ctor_get(v___x_4699_, 12);
v_debug_4712_ = lean_ctor_get_uint8(v___x_4699_, sizeof(void*)*13);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v___x_4699_, 10);
lean_dec(v_unused_4751_);
v___x_4714_ = v___x_4699_;
v_isShared_4715_ = v_isSharedCheck_4750_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_instanceOverrides_4711_);
lean_inc(v_canon_4710_);
lean_inc(v_extensions_4709_);
lean_inc(v_defEqI_4708_);
lean_inc(v_congrInfo_4707_);
lean_inc(v_getLevel_4706_);
lean_inc(v_inferType_4705_);
lean_inc(v_letValue_4704_);
lean_inc(v_proofInstInfoFVar_4703_);
lean_inc(v_proofInstInfo_4702_);
lean_inc(v_maxFVar_4701_);
lean_inc(v_share_4700_);
lean_dec(v___x_4699_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4750_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4716_ = lean_box(0);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 10, v___x_4716_);
v___x_4718_ = v___x_4714_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_share_4700_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_maxFVar_4701_);
lean_ctor_set(v_reuseFailAlloc_4749_, 2, v_proofInstInfo_4702_);
lean_ctor_set(v_reuseFailAlloc_4749_, 3, v_proofInstInfoFVar_4703_);
lean_ctor_set(v_reuseFailAlloc_4749_, 4, v_letValue_4704_);
lean_ctor_set(v_reuseFailAlloc_4749_, 5, v_inferType_4705_);
lean_ctor_set(v_reuseFailAlloc_4749_, 6, v_getLevel_4706_);
lean_ctor_set(v_reuseFailAlloc_4749_, 7, v_congrInfo_4707_);
lean_ctor_set(v_reuseFailAlloc_4749_, 8, v_defEqI_4708_);
lean_ctor_set(v_reuseFailAlloc_4749_, 9, v_extensions_4709_);
lean_ctor_set(v_reuseFailAlloc_4749_, 10, v___x_4716_);
lean_ctor_set(v_reuseFailAlloc_4749_, 11, v_canon_4710_);
lean_ctor_set(v_reuseFailAlloc_4749_, 12, v_instanceOverrides_4711_);
lean_ctor_set_uint8(v_reuseFailAlloc_4749_, sizeof(void*)*13, v_debug_4712_);
v___x_4718_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4719_; lean_object* v_r_4720_; 
v___x_4719_ = lean_st_ref_put(v_a_4691_, v___x_4718_);
lean_inc(v_a_4695_);
lean_inc_ref(v_a_4694_);
lean_inc(v_a_4693_);
lean_inc_ref(v_a_4692_);
lean_inc(v_a_4691_);
lean_inc_ref(v_a_4690_);
v_r_4720_ = lean_apply_7(v_x_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, lean_box(0));
if (lean_obj_tag(v_r_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4737_; 
v_a_4721_ = lean_ctor_get(v_r_4720_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v_r_4720_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4723_ = v_r_4720_;
v_isShared_4724_ = v_isSharedCheck_4737_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v_r_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4737_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
lean_inc(v_a_4721_);
if (v_isShared_4724_ == 0)
{
lean_ctor_set_tag(v___x_4723_, 1);
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
v___x_4727_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4691_, v_issues_4698_, v___x_4726_);
lean_dec_ref(v___x_4726_);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4734_ == 0)
{
lean_object* v_unused_4735_; 
v_unused_4735_ = lean_ctor_get(v___x_4727_, 0);
lean_dec(v_unused_4735_);
v___x_4729_ = v___x_4727_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_dec(v___x_4727_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 0, v_a_4721_);
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4721_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
v_a_4738_ = lean_ctor_get(v_r_4720_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v_r_4720_, 1);
v___x_4739_ = lean_box(0);
v___x_4740_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4691_, v_issues_4698_, v___x_4739_);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4747_ == 0)
{
lean_object* v_unused_4748_; 
v_unused_4748_ = lean_ctor_get(v___x_4740_, 0);
lean_dec(v_unused_4748_);
v___x_4742_ = v___x_4740_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_dec(v___x_4740_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set_tag(v___x_4742_, 1);
lean_ctor_set(v___x_4742_, 0, v_a_4738_);
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4738_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4761_, lean_object* v_x_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4771_, lean_object* v_x_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4771_, v_x_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4781_, lean_object* v_vals_4782_, lean_object* v_i_4783_, lean_object* v_k_4784_){
_start:
{
lean_object* v___x_4789_; uint8_t v___x_4790_; 
v___x_4789_ = lean_array_get_size(v_keys_4781_);
v___x_4790_ = lean_nat_dec_lt(v_i_4783_, v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
lean_dec(v_i_4783_);
v___x_4791_ = lean_box(0);
return v___x_4791_;
}
else
{
lean_object* v_fst_4792_; lean_object* v_snd_4793_; lean_object* v_k_x27_4794_; lean_object* v_fst_4795_; lean_object* v_snd_4796_; size_t v___x_4797_; size_t v___x_4798_; uint8_t v___x_4799_; 
v_fst_4792_ = lean_ctor_get(v_k_4784_, 0);
v_snd_4793_ = lean_ctor_get(v_k_4784_, 1);
v_k_x27_4794_ = lean_array_fget_borrowed(v_keys_4781_, v_i_4783_);
v_fst_4795_ = lean_ctor_get(v_k_x27_4794_, 0);
v_snd_4796_ = lean_ctor_get(v_k_x27_4794_, 1);
v___x_4797_ = lean_ptr_addr(v_fst_4792_);
v___x_4798_ = lean_ptr_addr(v_fst_4795_);
v___x_4799_ = lean_usize_dec_eq(v___x_4797_, v___x_4798_);
if (v___x_4799_ == 0)
{
goto v___jp_4785_;
}
else
{
size_t v___x_4800_; size_t v___x_4801_; uint8_t v___x_4802_; 
v___x_4800_ = lean_ptr_addr(v_snd_4793_);
v___x_4801_ = lean_ptr_addr(v_snd_4796_);
v___x_4802_ = lean_usize_dec_eq(v___x_4800_, v___x_4801_);
if (v___x_4802_ == 0)
{
goto v___jp_4785_;
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = lean_array_fget_borrowed(v_vals_4782_, v_i_4783_);
lean_dec(v_i_4783_);
lean_inc(v___x_4803_);
v___x_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
return v___x_4804_;
}
}
}
v___jp_4785_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = lean_unsigned_to_nat(1u);
v___x_4787_ = lean_nat_add(v_i_4783_, v___x_4786_);
lean_dec(v_i_4783_);
v_i_4783_ = v___x_4787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4805_, lean_object* v_vals_4806_, lean_object* v_i_4807_, lean_object* v_k_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4805_, v_vals_4806_, v_i_4807_, v_k_4808_);
lean_dec_ref(v_k_4808_);
lean_dec_ref(v_vals_4806_);
lean_dec_ref(v_keys_4805_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4810_, size_t v_x_4811_, lean_object* v_x_4812_){
_start:
{
if (lean_obj_tag(v_x_4810_) == 0)
{
lean_object* v_es_4813_; lean_object* v___x_4814_; size_t v___x_4815_; size_t v___x_4816_; lean_object* v_j_4817_; lean_object* v___x_4818_; 
v_es_4813_ = lean_ctor_get(v_x_4810_, 0);
v___x_4814_ = lean_box(2);
v___x_4815_ = ((size_t)31ULL);
v___x_4816_ = lean_usize_land(v_x_4811_, v___x_4815_);
v_j_4817_ = lean_usize_to_nat(v___x_4816_);
v___x_4818_ = lean_array_get_borrowed(v___x_4814_, v_es_4813_, v_j_4817_);
lean_dec(v_j_4817_);
switch(lean_obj_tag(v___x_4818_))
{
case 0:
{
lean_object* v_key_4819_; lean_object* v_val_4820_; lean_object* v_fst_4821_; lean_object* v_snd_4822_; lean_object* v_fst_4823_; lean_object* v_snd_4824_; size_t v___x_4825_; size_t v___x_4826_; uint8_t v___x_4827_; 
v_key_4819_ = lean_ctor_get(v___x_4818_, 0);
v_val_4820_ = lean_ctor_get(v___x_4818_, 1);
v_fst_4821_ = lean_ctor_get(v_x_4812_, 0);
v_snd_4822_ = lean_ctor_get(v_x_4812_, 1);
v_fst_4823_ = lean_ctor_get(v_key_4819_, 0);
v_snd_4824_ = lean_ctor_get(v_key_4819_, 1);
v___x_4825_ = lean_ptr_addr(v_fst_4821_);
v___x_4826_ = lean_ptr_addr(v_fst_4823_);
v___x_4827_ = lean_usize_dec_eq(v___x_4825_, v___x_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_box(0);
return v___x_4828_;
}
else
{
size_t v___x_4829_; size_t v___x_4830_; uint8_t v___x_4831_; 
v___x_4829_ = lean_ptr_addr(v_snd_4822_);
v___x_4830_ = lean_ptr_addr(v_snd_4824_);
v___x_4831_ = lean_usize_dec_eq(v___x_4829_, v___x_4830_);
if (v___x_4831_ == 0)
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_box(0);
return v___x_4832_;
}
else
{
lean_object* v___x_4833_; 
lean_inc(v_val_4820_);
v___x_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4833_, 0, v_val_4820_);
return v___x_4833_;
}
}
}
case 1:
{
lean_object* v_node_4834_; size_t v___x_4835_; size_t v___x_4836_; 
v_node_4834_ = lean_ctor_get(v___x_4818_, 0);
v___x_4835_ = ((size_t)5ULL);
v___x_4836_ = lean_usize_shift_right(v_x_4811_, v___x_4835_);
v_x_4810_ = v_node_4834_;
v_x_4811_ = v___x_4836_;
goto _start;
}
default: 
{
lean_object* v___x_4838_; 
v___x_4838_ = lean_box(0);
return v___x_4838_;
}
}
}
else
{
lean_object* v_ks_4839_; lean_object* v_vs_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v_ks_4839_ = lean_ctor_get(v_x_4810_, 0);
v_vs_4840_ = lean_ctor_get(v_x_4810_, 1);
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4839_, v_vs_4840_, v___x_4841_, v_x_4812_);
return v___x_4842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4843_, lean_object* v_x_4844_, lean_object* v_x_4845_){
_start:
{
size_t v_x_2905__boxed_4846_; lean_object* v_res_4847_; 
v_x_2905__boxed_4846_ = lean_unbox_usize(v_x_4844_);
lean_dec(v_x_4844_);
v_res_4847_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4843_, v_x_2905__boxed_4846_, v_x_4845_);
lean_dec_ref(v_x_4845_);
lean_dec_ref(v_x_4843_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4848_, lean_object* v_x_4849_){
_start:
{
lean_object* v_fst_4850_; lean_object* v_snd_4851_; size_t v___x_4852_; size_t v___x_4853_; size_t v___x_4854_; uint64_t v___x_4855_; size_t v___x_4856_; size_t v___x_4857_; uint64_t v___x_4858_; uint64_t v___x_4859_; size_t v___x_4860_; lean_object* v___x_4861_; 
v_fst_4850_ = lean_ctor_get(v_x_4849_, 0);
v_snd_4851_ = lean_ctor_get(v_x_4849_, 1);
v___x_4852_ = lean_ptr_addr(v_fst_4850_);
v___x_4853_ = ((size_t)3ULL);
v___x_4854_ = lean_usize_shift_right(v___x_4852_, v___x_4853_);
v___x_4855_ = lean_usize_to_uint64(v___x_4854_);
v___x_4856_ = lean_ptr_addr(v_snd_4851_);
v___x_4857_ = lean_usize_shift_right(v___x_4856_, v___x_4853_);
v___x_4858_ = lean_usize_to_uint64(v___x_4857_);
v___x_4859_ = lean_uint64_mix_hash(v___x_4855_, v___x_4858_);
v___x_4860_ = lean_uint64_to_usize(v___x_4859_);
v___x_4861_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4848_, v___x_4860_, v_x_4849_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4862_, lean_object* v_x_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4862_, v_x_4863_);
lean_dec_ref(v_x_4863_);
lean_dec_ref(v_x_4862_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4865_, lean_object* v_x_4866_, lean_object* v_x_4867_, lean_object* v_x_4868_){
_start:
{
lean_object* v_ks_4869_; lean_object* v_vs_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4906_; 
v_ks_4869_ = lean_ctor_get(v_x_4865_, 0);
v_vs_4870_ = lean_ctor_get(v_x_4865_, 1);
v_isSharedCheck_4906_ = !lean_is_exclusive(v_x_4865_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4872_ = v_x_4865_;
v_isShared_4873_ = v_isSharedCheck_4906_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_vs_4870_);
lean_inc(v_ks_4869_);
lean_dec(v_x_4865_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4906_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4881_; uint8_t v___x_4882_; 
v___x_4881_ = lean_array_get_size(v_ks_4869_);
v___x_4882_ = lean_nat_dec_lt(v_x_4866_, v___x_4881_);
if (v___x_4882_ == 0)
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
lean_del_object(v___x_4872_);
lean_dec(v_x_4866_);
v___x_4883_ = lean_array_push(v_ks_4869_, v_x_4867_);
v___x_4884_ = lean_array_push(v_vs_4870_, v_x_4868_);
v___x_4885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4883_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
return v___x_4885_;
}
else
{
lean_object* v_fst_4886_; lean_object* v_snd_4887_; lean_object* v_k_x27_4888_; lean_object* v_fst_4889_; lean_object* v_snd_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4905_; 
v_fst_4886_ = lean_ctor_get(v_x_4867_, 0);
v_snd_4887_ = lean_ctor_get(v_x_4867_, 1);
v_k_x27_4888_ = lean_array_fget(v_ks_4869_, v_x_4866_);
v_fst_4889_ = lean_ctor_get(v_k_x27_4888_, 0);
v_snd_4890_ = lean_ctor_get(v_k_x27_4888_, 1);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_k_x27_4888_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4892_ = v_k_x27_4888_;
v_isShared_4893_ = v_isSharedCheck_4905_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_snd_4890_);
lean_inc(v_fst_4889_);
lean_dec(v_k_x27_4888_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4905_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
size_t v___x_4894_; size_t v___x_4895_; uint8_t v___x_4896_; 
v___x_4894_ = lean_ptr_addr(v_fst_4886_);
v___x_4895_ = lean_ptr_addr(v_fst_4889_);
lean_dec(v_fst_4889_);
v___x_4896_ = lean_usize_dec_eq(v___x_4894_, v___x_4895_);
if (v___x_4896_ == 0)
{
lean_del_object(v___x_4892_);
lean_dec(v_snd_4890_);
goto v___jp_4874_;
}
else
{
size_t v___x_4897_; size_t v___x_4898_; uint8_t v___x_4899_; 
v___x_4897_ = lean_ptr_addr(v_snd_4887_);
v___x_4898_ = lean_ptr_addr(v_snd_4890_);
lean_dec(v_snd_4890_);
v___x_4899_ = lean_usize_dec_eq(v___x_4897_, v___x_4898_);
if (v___x_4899_ == 0)
{
lean_del_object(v___x_4892_);
goto v___jp_4874_;
}
else
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4903_; 
lean_del_object(v___x_4872_);
v___x_4900_ = lean_array_fset(v_ks_4869_, v_x_4866_, v_x_4867_);
v___x_4901_ = lean_array_fset(v_vs_4870_, v_x_4866_, v_x_4868_);
lean_dec(v_x_4866_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set_tag(v___x_4892_, 1);
lean_ctor_set(v___x_4892_, 1, v___x_4901_);
lean_ctor_set(v___x_4892_, 0, v___x_4900_);
v___x_4903_ = v___x_4892_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4900_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v___x_4901_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
}
v___jp_4874_:
{
lean_object* v___x_4876_; 
if (v_isShared_4873_ == 0)
{
v___x_4876_ = v___x_4872_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_ks_4869_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v_vs_4870_);
v___x_4876_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_unsigned_to_nat(1u);
v___x_4878_ = lean_nat_add(v_x_4866_, v___x_4877_);
lean_dec(v_x_4866_);
v_x_4865_ = v___x_4876_;
v_x_4866_ = v___x_4878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4907_, lean_object* v_k_4908_, lean_object* v_v_4909_){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = lean_unsigned_to_nat(0u);
v___x_4911_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4907_, v___x_4910_, v_k_4908_, v_v_4909_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4912_, size_t v_x_4913_, size_t v_x_4914_, lean_object* v_x_4915_, lean_object* v_x_4916_){
_start:
{
if (lean_obj_tag(v_x_4912_) == 0)
{
lean_object* v_es_4917_; size_t v___x_4918_; size_t v___x_4919_; lean_object* v_j_4920_; lean_object* v___x_4921_; uint8_t v___x_4922_; 
v_es_4917_ = lean_ctor_get(v_x_4912_, 0);
v___x_4918_ = ((size_t)31ULL);
v___x_4919_ = lean_usize_land(v_x_4913_, v___x_4918_);
v_j_4920_ = lean_usize_to_nat(v___x_4919_);
v___x_4921_ = lean_array_get_size(v_es_4917_);
v___x_4922_ = lean_nat_dec_lt(v_j_4920_, v___x_4921_);
if (v___x_4922_ == 0)
{
lean_dec(v_j_4920_);
lean_dec(v_x_4916_);
lean_dec_ref(v_x_4915_);
return v_x_4912_;
}
else
{
lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4971_; 
lean_inc_ref(v_es_4917_);
v_isSharedCheck_4971_ = !lean_is_exclusive(v_x_4912_);
if (v_isSharedCheck_4971_ == 0)
{
lean_object* v_unused_4972_; 
v_unused_4972_ = lean_ctor_get(v_x_4912_, 0);
lean_dec(v_unused_4972_);
v___x_4924_ = v_x_4912_;
v_isShared_4925_ = v_isSharedCheck_4971_;
goto v_resetjp_4923_;
}
else
{
lean_dec(v_x_4912_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4971_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v_v_4926_; lean_object* v___x_4927_; lean_object* v_xs_x27_4928_; lean_object* v___y_4930_; 
v_v_4926_ = lean_array_fget(v_es_4917_, v_j_4920_);
v___x_4927_ = lean_box(0);
v_xs_x27_4928_ = lean_array_fset(v_es_4917_, v_j_4920_, v___x_4927_);
switch(lean_obj_tag(v_v_4926_))
{
case 0:
{
lean_object* v_key_4935_; lean_object* v_val_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4956_; 
v_key_4935_ = lean_ctor_get(v_v_4926_, 0);
v_val_4936_ = lean_ctor_get(v_v_4926_, 1);
v_isSharedCheck_4956_ = !lean_is_exclusive(v_v_4926_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4938_ = v_v_4926_;
v_isShared_4939_ = v_isSharedCheck_4956_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_val_4936_);
lean_inc(v_key_4935_);
lean_dec(v_v_4926_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4956_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v_fst_4943_; lean_object* v_snd_4944_; lean_object* v_fst_4945_; lean_object* v_snd_4946_; size_t v___x_4947_; size_t v___x_4948_; uint8_t v___x_4949_; 
v_fst_4943_ = lean_ctor_get(v_x_4915_, 0);
v_snd_4944_ = lean_ctor_get(v_x_4915_, 1);
v_fst_4945_ = lean_ctor_get(v_key_4935_, 0);
v_snd_4946_ = lean_ctor_get(v_key_4935_, 1);
v___x_4947_ = lean_ptr_addr(v_fst_4943_);
v___x_4948_ = lean_ptr_addr(v_fst_4945_);
v___x_4949_ = lean_usize_dec_eq(v___x_4947_, v___x_4948_);
if (v___x_4949_ == 0)
{
lean_del_object(v___x_4938_);
goto v___jp_4940_;
}
else
{
size_t v___x_4950_; size_t v___x_4951_; uint8_t v___x_4952_; 
v___x_4950_ = lean_ptr_addr(v_snd_4944_);
v___x_4951_ = lean_ptr_addr(v_snd_4946_);
v___x_4952_ = lean_usize_dec_eq(v___x_4950_, v___x_4951_);
if (v___x_4952_ == 0)
{
lean_del_object(v___x_4938_);
goto v___jp_4940_;
}
else
{
lean_object* v___x_4954_; 
lean_dec(v_val_4936_);
lean_dec(v_key_4935_);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 1, v_x_4916_);
lean_ctor_set(v___x_4938_, 0, v_x_4915_);
v___x_4954_ = v___x_4938_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_x_4915_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_x_4916_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
v___y_4930_ = v___x_4954_;
goto v___jp_4929_;
}
}
}
v___jp_4940_:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4935_, v_val_4936_, v_x_4915_, v_x_4916_);
v___x_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4941_);
v___y_4930_ = v___x_4942_;
goto v___jp_4929_;
}
}
}
case 1:
{
lean_object* v_node_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4969_; 
v_node_4957_ = lean_ctor_get(v_v_4926_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_v_4926_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4959_ = v_v_4926_;
v_isShared_4960_ = v_isSharedCheck_4969_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_node_4957_);
lean_dec(v_v_4926_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4969_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
size_t v___x_4961_; size_t v___x_4962_; size_t v___x_4963_; size_t v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4967_; 
v___x_4961_ = ((size_t)5ULL);
v___x_4962_ = lean_usize_shift_right(v_x_4913_, v___x_4961_);
v___x_4963_ = ((size_t)1ULL);
v___x_4964_ = lean_usize_add(v_x_4914_, v___x_4963_);
v___x_4965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4957_, v___x_4962_, v___x_4964_, v_x_4915_, v_x_4916_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4965_);
v___x_4967_ = v___x_4959_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4965_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
v___y_4930_ = v___x_4967_;
goto v___jp_4929_;
}
}
}
default: 
{
lean_object* v___x_4970_; 
v___x_4970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4970_, 0, v_x_4915_);
lean_ctor_set(v___x_4970_, 1, v_x_4916_);
v___y_4930_ = v___x_4970_;
goto v___jp_4929_;
}
}
v___jp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4931_ = lean_array_fset(v_xs_x27_4928_, v_j_4920_, v___y_4930_);
lean_dec(v_j_4920_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 0, v___x_4931_);
v___x_4933_ = v___x_4924_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
else
{
lean_object* v_ks_4973_; lean_object* v_vs_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4992_; 
v_ks_4973_ = lean_ctor_get(v_x_4912_, 0);
v_vs_4974_ = lean_ctor_get(v_x_4912_, 1);
v_isSharedCheck_4992_ = !lean_is_exclusive(v_x_4912_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4976_ = v_x_4912_;
v_isShared_4977_ = v_isSharedCheck_4992_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_vs_4974_);
lean_inc(v_ks_4973_);
lean_dec(v_x_4912_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4992_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4979_; 
if (v_isShared_4977_ == 0)
{
v___x_4979_ = v___x_4976_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_ks_4973_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_vs_4974_);
v___x_4979_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v_newNode_4980_; size_t v___x_4981_; uint8_t v___x_4982_; 
v_newNode_4980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4979_, v_x_4915_, v_x_4916_);
v___x_4981_ = ((size_t)7ULL);
v___x_4982_ = lean_usize_dec_le(v___x_4981_, v_x_4914_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4983_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4980_);
v___x_4984_ = lean_unsigned_to_nat(4u);
v___x_4985_ = lean_nat_dec_lt(v___x_4983_, v___x_4984_);
lean_dec(v___x_4983_);
if (v___x_4985_ == 0)
{
lean_object* v_ks_4986_; lean_object* v_vs_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_ks_4986_ = lean_ctor_get(v_newNode_4980_, 0);
lean_inc_ref(v_ks_4986_);
v_vs_4987_ = lean_ctor_get(v_newNode_4980_, 1);
lean_inc_ref(v_vs_4987_);
lean_dec_ref(v_newNode_4980_);
v___x_4988_ = lean_unsigned_to_nat(0u);
v___x_4989_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0);
v___x_4990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4914_, v_ks_4986_, v_vs_4987_, v___x_4988_, v___x_4989_);
lean_dec_ref(v_vs_4987_);
lean_dec_ref(v_ks_4986_);
return v___x_4990_;
}
else
{
return v_newNode_4980_;
}
}
else
{
return v_newNode_4980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4993_, lean_object* v_keys_4994_, lean_object* v_vals_4995_, lean_object* v_i_4996_, lean_object* v_entries_4997_){
_start:
{
lean_object* v___x_4998_; uint8_t v___x_4999_; 
v___x_4998_ = lean_array_get_size(v_keys_4994_);
v___x_4999_ = lean_nat_dec_lt(v_i_4996_, v___x_4998_);
if (v___x_4999_ == 0)
{
lean_dec(v_i_4996_);
return v_entries_4997_;
}
else
{
lean_object* v_k_5000_; lean_object* v_fst_5001_; lean_object* v_snd_5002_; lean_object* v_v_5003_; size_t v___x_5004_; size_t v___x_5005_; size_t v___x_5006_; uint64_t v___x_5007_; size_t v___x_5008_; size_t v___x_5009_; uint64_t v___x_5010_; uint64_t v___x_5011_; size_t v_h_5012_; size_t v___x_5013_; lean_object* v___x_5014_; size_t v___x_5015_; size_t v___x_5016_; size_t v___x_5017_; size_t v_h_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v_k_5000_ = lean_array_fget_borrowed(v_keys_4994_, v_i_4996_);
v_fst_5001_ = lean_ctor_get(v_k_5000_, 0);
v_snd_5002_ = lean_ctor_get(v_k_5000_, 1);
v_v_5003_ = lean_array_fget_borrowed(v_vals_4995_, v_i_4996_);
v___x_5004_ = lean_ptr_addr(v_fst_5001_);
v___x_5005_ = ((size_t)3ULL);
v___x_5006_ = lean_usize_shift_right(v___x_5004_, v___x_5005_);
v___x_5007_ = lean_usize_to_uint64(v___x_5006_);
v___x_5008_ = lean_ptr_addr(v_snd_5002_);
v___x_5009_ = lean_usize_shift_right(v___x_5008_, v___x_5005_);
v___x_5010_ = lean_usize_to_uint64(v___x_5009_);
v___x_5011_ = lean_uint64_mix_hash(v___x_5007_, v___x_5010_);
v_h_5012_ = lean_uint64_to_usize(v___x_5011_);
v___x_5013_ = ((size_t)5ULL);
v___x_5014_ = lean_unsigned_to_nat(1u);
v___x_5015_ = ((size_t)1ULL);
v___x_5016_ = lean_usize_sub(v_depth_4993_, v___x_5015_);
v___x_5017_ = lean_usize_mul(v___x_5013_, v___x_5016_);
v_h_5018_ = lean_usize_shift_right(v_h_5012_, v___x_5017_);
v___x_5019_ = lean_nat_add(v_i_4996_, v___x_5014_);
lean_dec(v_i_4996_);
lean_inc(v_v_5003_);
lean_inc(v_k_5000_);
v___x_5020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4997_, v_h_5018_, v_depth_4993_, v_k_5000_, v_v_5003_);
v_i_4996_ = v___x_5019_;
v_entries_4997_ = v___x_5020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_5022_, lean_object* v_keys_5023_, lean_object* v_vals_5024_, lean_object* v_i_5025_, lean_object* v_entries_5026_){
_start:
{
size_t v_depth_boxed_5027_; lean_object* v_res_5028_; 
v_depth_boxed_5027_ = lean_unbox_usize(v_depth_5022_);
lean_dec(v_depth_5022_);
v_res_5028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_5027_, v_keys_5023_, v_vals_5024_, v_i_5025_, v_entries_5026_);
lean_dec_ref(v_vals_5024_);
lean_dec_ref(v_keys_5023_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_5029_, lean_object* v_x_5030_, lean_object* v_x_5031_, lean_object* v_x_5032_, lean_object* v_x_5033_){
_start:
{
size_t v_x_3110__boxed_5034_; size_t v_x_3111__boxed_5035_; lean_object* v_res_5036_; 
v_x_3110__boxed_5034_ = lean_unbox_usize(v_x_5030_);
lean_dec(v_x_5030_);
v_x_3111__boxed_5035_ = lean_unbox_usize(v_x_5031_);
lean_dec(v_x_5031_);
v_res_5036_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_5029_, v_x_3110__boxed_5034_, v_x_3111__boxed_5035_, v_x_5032_, v_x_5033_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_5037_, lean_object* v_x_5038_, lean_object* v_x_5039_){
_start:
{
lean_object* v_fst_5040_; lean_object* v_snd_5041_; size_t v___x_5042_; size_t v___x_5043_; size_t v___x_5044_; uint64_t v___x_5045_; size_t v___x_5046_; size_t v___x_5047_; uint64_t v___x_5048_; uint64_t v___x_5049_; size_t v___x_5050_; size_t v___x_5051_; lean_object* v___x_5052_; 
v_fst_5040_ = lean_ctor_get(v_x_5038_, 0);
v_snd_5041_ = lean_ctor_get(v_x_5038_, 1);
v___x_5042_ = lean_ptr_addr(v_fst_5040_);
v___x_5043_ = ((size_t)3ULL);
v___x_5044_ = lean_usize_shift_right(v___x_5042_, v___x_5043_);
v___x_5045_ = lean_usize_to_uint64(v___x_5044_);
v___x_5046_ = lean_ptr_addr(v_snd_5041_);
v___x_5047_ = lean_usize_shift_right(v___x_5046_, v___x_5043_);
v___x_5048_ = lean_usize_to_uint64(v___x_5047_);
v___x_5049_ = lean_uint64_mix_hash(v___x_5045_, v___x_5048_);
v___x_5050_ = lean_uint64_to_usize(v___x_5049_);
v___x_5051_ = ((size_t)1ULL);
v___x_5052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_5037_, v___x_5050_, v___x_5051_, v_x_5038_, v_x_5039_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_5053_, lean_object* v_t_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_key_5061_; lean_object* v___x_5062_; lean_object* v_defEqI_5063_; lean_object* v___x_5064_; 
lean_inc_ref(v_t_5054_);
lean_inc_ref(v_s_5053_);
v_key_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_5061_, 0, v_s_5053_);
lean_ctor_set(v_key_5061_, 1, v_t_5054_);
v___x_5062_ = lean_st_ref_get(v_a_5055_);
v_defEqI_5063_ = lean_ctor_get(v___x_5062_, 8);
lean_inc_ref(v_defEqI_5063_);
lean_dec(v___x_5062_);
v___x_5064_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_5063_, v_key_5061_);
lean_dec_ref(v_defEqI_5063_);
if (lean_obj_tag(v___x_5064_) == 1)
{
lean_object* v_val_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
lean_dec_ref_known(v_key_5061_, 2);
lean_dec_ref(v_t_5054_);
lean_dec_ref(v_s_5053_);
v_val_5065_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5064_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_val_5065_);
lean_dec(v___x_5064_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
lean_ctor_set_tag(v___x_5067_, 0);
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_val_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
else
{
lean_object* v___x_5073_; 
lean_dec(v___x_5064_);
v___x_5073_ = l_Lean_Meta_isDefEqI(v_s_5053_, v_t_5054_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5105_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5076_ = v___x_5073_;
v_isShared_5077_ = v_isSharedCheck_5105_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5073_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5105_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; lean_object* v_share_5079_; lean_object* v_maxFVar_5080_; lean_object* v_proofInstInfo_5081_; lean_object* v_proofInstInfoFVar_5082_; lean_object* v_letValue_5083_; lean_object* v_inferType_5084_; lean_object* v_getLevel_5085_; lean_object* v_congrInfo_5086_; lean_object* v_defEqI_5087_; lean_object* v_extensions_5088_; lean_object* v_issues_5089_; lean_object* v_canon_5090_; lean_object* v_instanceOverrides_5091_; uint8_t v_debug_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5104_; 
v___x_5078_ = lean_st_ref_take(v_a_5055_);
v_share_5079_ = lean_ctor_get(v___x_5078_, 0);
v_maxFVar_5080_ = lean_ctor_get(v___x_5078_, 1);
v_proofInstInfo_5081_ = lean_ctor_get(v___x_5078_, 2);
v_proofInstInfoFVar_5082_ = lean_ctor_get(v___x_5078_, 3);
v_letValue_5083_ = lean_ctor_get(v___x_5078_, 4);
v_inferType_5084_ = lean_ctor_get(v___x_5078_, 5);
v_getLevel_5085_ = lean_ctor_get(v___x_5078_, 6);
v_congrInfo_5086_ = lean_ctor_get(v___x_5078_, 7);
v_defEqI_5087_ = lean_ctor_get(v___x_5078_, 8);
v_extensions_5088_ = lean_ctor_get(v___x_5078_, 9);
v_issues_5089_ = lean_ctor_get(v___x_5078_, 10);
v_canon_5090_ = lean_ctor_get(v___x_5078_, 11);
v_instanceOverrides_5091_ = lean_ctor_get(v___x_5078_, 12);
v_debug_5092_ = lean_ctor_get_uint8(v___x_5078_, sizeof(void*)*13);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5094_ = v___x_5078_;
v_isShared_5095_ = v_isSharedCheck_5104_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_instanceOverrides_5091_);
lean_inc(v_canon_5090_);
lean_inc(v_issues_5089_);
lean_inc(v_extensions_5088_);
lean_inc(v_defEqI_5087_);
lean_inc(v_congrInfo_5086_);
lean_inc(v_getLevel_5085_);
lean_inc(v_inferType_5084_);
lean_inc(v_letValue_5083_);
lean_inc(v_proofInstInfoFVar_5082_);
lean_inc(v_proofInstInfo_5081_);
lean_inc(v_maxFVar_5080_);
lean_inc(v_share_5079_);
lean_dec(v___x_5078_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5104_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5096_; lean_object* v___x_5098_; 
lean_inc(v_a_5074_);
v___x_5096_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_5087_, v_key_5061_, v_a_5074_);
if (v_isShared_5095_ == 0)
{
lean_ctor_set(v___x_5094_, 8, v___x_5096_);
v___x_5098_ = v___x_5094_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_share_5079_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_maxFVar_5080_);
lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_proofInstInfo_5081_);
lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_proofInstInfoFVar_5082_);
lean_ctor_set(v_reuseFailAlloc_5103_, 4, v_letValue_5083_);
lean_ctor_set(v_reuseFailAlloc_5103_, 5, v_inferType_5084_);
lean_ctor_set(v_reuseFailAlloc_5103_, 6, v_getLevel_5085_);
lean_ctor_set(v_reuseFailAlloc_5103_, 7, v_congrInfo_5086_);
lean_ctor_set(v_reuseFailAlloc_5103_, 8, v___x_5096_);
lean_ctor_set(v_reuseFailAlloc_5103_, 9, v_extensions_5088_);
lean_ctor_set(v_reuseFailAlloc_5103_, 10, v_issues_5089_);
lean_ctor_set(v_reuseFailAlloc_5103_, 11, v_canon_5090_);
lean_ctor_set(v_reuseFailAlloc_5103_, 12, v_instanceOverrides_5091_);
lean_ctor_set_uint8(v_reuseFailAlloc_5103_, sizeof(void*)*13, v_debug_5092_);
v___x_5098_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5099_ = lean_st_ref_put(v_a_5055_, v___x_5098_);
if (v_isShared_5077_ == 0)
{
v___x_5101_ = v___x_5076_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5074_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_5061_, 2);
return v___x_5073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_5106_, lean_object* v_t_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_5106_, v_t_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_);
lean_dec(v_a_5112_);
lean_dec_ref(v_a_5111_);
lean_dec(v_a_5110_);
lean_dec_ref(v_a_5109_);
lean_dec(v_a_5108_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_5115_, lean_object* v_t_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_5115_, v_t_5116_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_5125_, lean_object* v_t_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_Meta_Sym_isDefEqI(v_s_5125_, v_t_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
lean_dec(v_a_5130_);
lean_dec_ref(v_a_5129_);
lean_dec(v_a_5128_);
lean_dec_ref(v_a_5127_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_5135_, lean_object* v_x_5136_, lean_object* v_x_5137_){
_start:
{
lean_object* v___x_5138_; 
v___x_5138_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_5136_, v_x_5137_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_5139_, lean_object* v_x_5140_, lean_object* v_x_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_5139_, v_x_5140_, v_x_5141_);
lean_dec_ref(v_x_5141_);
lean_dec_ref(v_x_5140_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_5143_, lean_object* v_x_5144_, lean_object* v_x_5145_, lean_object* v_x_5146_){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_5144_, v_x_5145_, v_x_5146_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_5148_, lean_object* v_x_5149_, size_t v_x_5150_, lean_object* v_x_5151_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_5149_, v_x_5150_, v_x_5151_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5153_, lean_object* v_x_5154_, lean_object* v_x_5155_, lean_object* v_x_5156_){
_start:
{
size_t v_x_3405__boxed_5157_; lean_object* v_res_5158_; 
v_x_3405__boxed_5157_ = lean_unbox_usize(v_x_5155_);
lean_dec(v_x_5155_);
v_res_5158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_5153_, v_x_5154_, v_x_3405__boxed_5157_, v_x_5156_);
lean_dec_ref(v_x_5156_);
lean_dec_ref(v_x_5154_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_5159_, lean_object* v_x_5160_, size_t v_x_5161_, size_t v_x_5162_, lean_object* v_x_5163_, lean_object* v_x_5164_){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_5160_, v_x_5161_, v_x_5162_, v_x_5163_, v_x_5164_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5166_, lean_object* v_x_5167_, lean_object* v_x_5168_, lean_object* v_x_5169_, lean_object* v_x_5170_, lean_object* v_x_5171_){
_start:
{
size_t v_x_3416__boxed_5172_; size_t v_x_3417__boxed_5173_; lean_object* v_res_5174_; 
v_x_3416__boxed_5172_ = lean_unbox_usize(v_x_5168_);
lean_dec(v_x_5168_);
v_x_3417__boxed_5173_ = lean_unbox_usize(v_x_5169_);
lean_dec(v_x_5169_);
v_res_5174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_5166_, v_x_5167_, v_x_3416__boxed_5172_, v_x_3417__boxed_5173_, v_x_5170_, v_x_5171_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5175_, lean_object* v_keys_5176_, lean_object* v_vals_5177_, lean_object* v_heq_5178_, lean_object* v_i_5179_, lean_object* v_k_5180_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_5176_, v_vals_5177_, v_i_5179_, v_k_5180_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5182_, lean_object* v_keys_5183_, lean_object* v_vals_5184_, lean_object* v_heq_5185_, lean_object* v_i_5186_, lean_object* v_k_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_5182_, v_keys_5183_, v_vals_5184_, v_heq_5185_, v_i_5186_, v_k_5187_);
lean_dec_ref(v_k_5187_);
lean_dec_ref(v_vals_5184_);
lean_dec_ref(v_keys_5183_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_5189_, lean_object* v_n_5190_, lean_object* v_k_5191_, lean_object* v_v_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_5190_, v_k_5191_, v_v_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_5194_, size_t v_depth_5195_, lean_object* v_keys_5196_, lean_object* v_vals_5197_, lean_object* v_heq_5198_, lean_object* v_i_5199_, lean_object* v_entries_5200_){
_start:
{
lean_object* v___x_5201_; 
v___x_5201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_5195_, v_keys_5196_, v_vals_5197_, v_i_5199_, v_entries_5200_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_5202_, lean_object* v_depth_5203_, lean_object* v_keys_5204_, lean_object* v_vals_5205_, lean_object* v_heq_5206_, lean_object* v_i_5207_, lean_object* v_entries_5208_){
_start:
{
size_t v_depth_boxed_5209_; lean_object* v_res_5210_; 
v_depth_boxed_5209_ = lean_unbox_usize(v_depth_5203_);
lean_dec(v_depth_5203_);
v_res_5210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_5202_, v_depth_boxed_5209_, v_keys_5204_, v_vals_5205_, v_heq_5206_, v_i_5207_, v_entries_5208_);
lean_dec_ref(v_vals_5205_);
lean_dec_ref(v_keys_5204_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_5211_, lean_object* v_x_5212_, lean_object* v_x_5213_, lean_object* v_x_5214_, lean_object* v_x_5215_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_5212_, v_x_5213_, v_x_5214_, v_x_5215_);
return v___x_5216_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0(void){
_start:
{
lean_object* v___x_5217_; lean_object* v___f_5218_; 
v___x_5217_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_5218_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5218_, 0, v___x_5217_);
return v___f_5218_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1(void){
_start:
{
lean_object* v___x_5219_; lean_object* v___f_5220_; 
v___x_5219_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_5220_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5220_, 0, v___x_5219_);
return v___f_5220_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2(void){
_start:
{
lean_object* v___f_5221_; lean_object* v___f_5222_; lean_object* v___x_5223_; 
v___f_5221_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1);
v___f_5222_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0);
v___x_5223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___f_5222_);
lean_ctor_set(v___x_5223_, 1, v___f_5221_);
return v___x_5223_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3(void){
_start:
{
lean_object* v___x_5224_; lean_object* v___f_5225_; 
v___x_5224_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_5225_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5225_, 0, v___x_5224_);
return v___f_5225_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4(void){
_start:
{
lean_object* v___x_5226_; lean_object* v___f_5227_; 
v___x_5226_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_5227_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5227_, 0, v___x_5226_);
return v___f_5227_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5(void){
_start:
{
lean_object* v___f_5228_; lean_object* v___f_5229_; lean_object* v___x_5230_; 
v___f_5228_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4);
v___f_5229_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3);
v___x_5230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5230_, 0, v___f_5229_);
lean_ctor_set(v___x_5230_, 1, v___f_5228_);
return v___x_5230_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6(void){
_start:
{
lean_object* v___x_5231_; lean_object* v___f_5232_; 
v___x_5231_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_5232_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5232_, 0, v___x_5231_);
return v___f_5232_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7(void){
_start:
{
lean_object* v___x_5233_; lean_object* v___f_5234_; 
v___x_5233_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_5234_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5234_, 0, v___x_5233_);
return v___f_5234_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8(void){
_start:
{
lean_object* v___f_5235_; lean_object* v___f_5236_; lean_object* v___x_5237_; 
v___f_5235_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7);
v___f_5236_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6);
v___x_5237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5237_, 0, v___f_5236_);
lean_ctor_set(v___x_5237_, 1, v___f_5235_);
return v___x_5237_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9(void){
_start:
{
lean_object* v___x_5238_; lean_object* v___f_5239_; 
v___x_5238_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_5239_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5239_, 0, v___x_5238_);
return v___f_5239_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10(void){
_start:
{
lean_object* v___x_5240_; lean_object* v___f_5241_; 
v___x_5240_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_5241_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5241_, 0, v___x_5240_);
return v___f_5241_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11(void){
_start:
{
lean_object* v___f_5242_; lean_object* v___f_5243_; lean_object* v___x_5244_; 
v___f_5242_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10);
v___f_5243_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9);
v___x_5244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___f_5243_);
lean_ctor_set(v___x_5244_, 1, v___f_5242_);
return v___x_5244_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16(void){
_start:
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5249_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_5250_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5251_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_5252_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_5251_, v___x_5250_, v___x_5249_);
return v___x_5252_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17(void){
_start:
{
lean_object* v___x_5253_; lean_object* v___f_5254_; lean_object* v___f_5255_; lean_object* v___x_5256_; 
v___x_5253_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16);
v___f_5254_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5255_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_5256_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_5255_, v___f_5254_, v___x_5253_);
return v___x_5256_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18(void){
_start:
{
lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5257_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17);
v___x_5258_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5259_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_5260_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_5259_, v___x_5258_, v___x_5257_);
return v___x_5260_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19(void){
_start:
{
lean_object* v___x_5261_; lean_object* v___f_5262_; lean_object* v___f_5263_; lean_object* v___x_5264_; 
v___x_5261_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18);
v___f_5262_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5263_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_5264_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_5263_, v___f_5262_, v___x_5261_);
return v___x_5264_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20(void){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___f_5267_; 
v___x_5265_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5266_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_5267_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5267_, 0, v___x_5266_);
lean_closure_set(v___f_5267_, 1, v___x_5265_);
return v___f_5267_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21(void){
_start:
{
lean_object* v___f_5268_; lean_object* v___f_5269_; lean_object* v___f_5270_; 
v___f_5268_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5269_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20);
v___f_5270_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5270_, 0, v___f_5269_);
lean_closure_set(v___f_5270_, 1, v___f_5268_);
return v___f_5270_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23(void){
_start:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22));
v___x_5273_ = l_Lean_stringToMessageData(v___x_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg(){
_start:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v_toApplicative_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5344_; 
v___x_5275_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_5276_ = l_StateRefT_x27_instMonad___redArg(v___x_5275_);
v_toApplicative_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5344_ == 0)
{
lean_object* v_unused_5345_; 
v_unused_5345_ = lean_ctor_get(v___x_5276_, 1);
lean_dec(v_unused_5345_);
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5344_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_toApplicative_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5344_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_toFunctor_5281_; lean_object* v_toSeq_5282_; lean_object* v_toSeqLeft_5283_; lean_object* v_toSeqRight_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5342_; 
v_toFunctor_5281_ = lean_ctor_get(v_toApplicative_5277_, 0);
v_toSeq_5282_ = lean_ctor_get(v_toApplicative_5277_, 2);
v_toSeqLeft_5283_ = lean_ctor_get(v_toApplicative_5277_, 3);
v_toSeqRight_5284_ = lean_ctor_get(v_toApplicative_5277_, 4);
v_isSharedCheck_5342_ = !lean_is_exclusive(v_toApplicative_5277_);
if (v_isSharedCheck_5342_ == 0)
{
lean_object* v_unused_5343_; 
v_unused_5343_ = lean_ctor_get(v_toApplicative_5277_, 1);
lean_dec(v_unused_5343_);
v___x_5286_ = v_toApplicative_5277_;
v_isShared_5287_ = v_isSharedCheck_5342_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_toSeqRight_5284_);
lean_inc(v_toSeqLeft_5283_);
lean_inc(v_toSeq_5282_);
lean_inc(v_toFunctor_5281_);
lean_dec(v_toApplicative_5277_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5342_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___f_5288_; lean_object* v___f_5289_; lean_object* v___f_5290_; lean_object* v___f_5291_; lean_object* v___x_5292_; lean_object* v___f_5293_; lean_object* v___f_5294_; lean_object* v___f_5295_; lean_object* v___x_5297_; 
v___f_5288_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_5289_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_5281_);
v___f_5290_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5290_, 0, v_toFunctor_5281_);
v___f_5291_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5291_, 0, v_toFunctor_5281_);
v___x_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___f_5290_);
lean_ctor_set(v___x_5292_, 1, v___f_5291_);
v___f_5293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5293_, 0, v_toSeqRight_5284_);
v___f_5294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5294_, 0, v_toSeqLeft_5283_);
v___f_5295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5295_, 0, v_toSeq_5282_);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 4, v___f_5293_);
lean_ctor_set(v___x_5286_, 3, v___f_5294_);
lean_ctor_set(v___x_5286_, 2, v___f_5295_);
lean_ctor_set(v___x_5286_, 1, v___f_5288_);
lean_ctor_set(v___x_5286_, 0, v___x_5292_);
v___x_5297_ = v___x_5286_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v___f_5288_);
lean_ctor_set(v_reuseFailAlloc_5341_, 2, v___f_5295_);
lean_ctor_set(v_reuseFailAlloc_5341_, 3, v___f_5294_);
lean_ctor_set(v_reuseFailAlloc_5341_, 4, v___f_5293_);
v___x_5297_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
lean_object* v___x_5299_; 
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 1, v___f_5289_);
lean_ctor_set(v___x_5279_, 0, v___x_5297_);
v___x_5299_ = v___x_5279_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v___f_5289_);
v___x_5299_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v_toApplicative_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5338_; 
v___x_5300_ = l_StateRefT_x27_instMonad___redArg(v___x_5299_);
v_toApplicative_5301_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5338_ == 0)
{
lean_object* v_unused_5339_; 
v_unused_5339_ = lean_ctor_get(v___x_5300_, 1);
lean_dec(v_unused_5339_);
v___x_5303_ = v___x_5300_;
v_isShared_5304_ = v_isSharedCheck_5338_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_toApplicative_5301_);
lean_dec(v___x_5300_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5338_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v_toFunctor_5305_; lean_object* v_toSeq_5306_; lean_object* v_toSeqLeft_5307_; lean_object* v_toSeqRight_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5336_; 
v_toFunctor_5305_ = lean_ctor_get(v_toApplicative_5301_, 0);
v_toSeq_5306_ = lean_ctor_get(v_toApplicative_5301_, 2);
v_toSeqLeft_5307_ = lean_ctor_get(v_toApplicative_5301_, 3);
v_toSeqRight_5308_ = lean_ctor_get(v_toApplicative_5301_, 4);
v_isSharedCheck_5336_ = !lean_is_exclusive(v_toApplicative_5301_);
if (v_isSharedCheck_5336_ == 0)
{
lean_object* v_unused_5337_; 
v_unused_5337_ = lean_ctor_get(v_toApplicative_5301_, 1);
lean_dec(v_unused_5337_);
v___x_5310_ = v_toApplicative_5301_;
v_isShared_5311_ = v_isSharedCheck_5336_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_toSeqRight_5308_);
lean_inc(v_toSeqLeft_5307_);
lean_inc(v_toSeq_5306_);
lean_inc(v_toFunctor_5305_);
lean_dec(v_toApplicative_5301_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5336_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___f_5312_; lean_object* v___f_5313_; lean_object* v___f_5314_; lean_object* v___f_5315_; lean_object* v___x_5316_; lean_object* v___f_5317_; lean_object* v___f_5318_; lean_object* v___f_5319_; lean_object* v___x_5321_; 
v___f_5312_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_5313_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_5305_);
v___f_5314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5314_, 0, v_toFunctor_5305_);
v___f_5315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5315_, 0, v_toFunctor_5305_);
v___x_5316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___f_5314_);
lean_ctor_set(v___x_5316_, 1, v___f_5315_);
v___f_5317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5317_, 0, v_toSeqRight_5308_);
v___f_5318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5318_, 0, v_toSeqLeft_5307_);
v___f_5319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5319_, 0, v_toSeq_5306_);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 4, v___f_5317_);
lean_ctor_set(v___x_5310_, 3, v___f_5318_);
lean_ctor_set(v___x_5310_, 2, v___f_5319_);
lean_ctor_set(v___x_5310_, 1, v___f_5312_);
lean_ctor_set(v___x_5310_, 0, v___x_5316_);
v___x_5321_ = v___x_5310_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5316_);
lean_ctor_set(v_reuseFailAlloc_5335_, 1, v___f_5312_);
lean_ctor_set(v_reuseFailAlloc_5335_, 2, v___f_5319_);
lean_ctor_set(v_reuseFailAlloc_5335_, 3, v___f_5318_);
lean_ctor_set(v_reuseFailAlloc_5335_, 4, v___f_5317_);
v___x_5321_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
lean_object* v___x_5323_; 
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 1, v___f_5313_);
lean_ctor_set(v___x_5303_, 0, v___x_5321_);
v___x_5323_ = v___x_5303_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v___f_5313_);
v___x_5323_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v_toMonadRef_5328_; lean_object* v___f_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5324_ = l_StateRefT_x27_instMonad___redArg(v___x_5323_);
v___x_5325_ = l_ReaderT_instMonad___redArg(v___x_5324_);
v___x_5326_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11);
v___x_5327_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19);
v_toMonadRef_5328_ = lean_ctor_get(v___x_5327_, 0);
v___f_5329_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21);
lean_inc_ref(v___x_5325_);
v___x_5330_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_5329_, v___x_5325_);
lean_inc_ref(v_toMonadRef_5328_);
v___x_5331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5326_);
lean_ctor_set(v___x_5331_, 1, v_toMonadRef_5328_);
lean_ctor_set(v___x_5331_, 2, v___x_5330_);
v___x_5332_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23);
v___x_5333_ = l_Lean_throwError___redArg(v___x_5325_, v___x_5331_, v___x_5332_);
return v___x_5333_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object* v___dummy_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v_res_5347_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_5348_; 
v___x_5348_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_5349_){
_start:
{
lean_object* v___x_5350_; 
v___x_5350_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_5351_, lean_object* v_extensions_5352_){
_start:
{
lean_object* v_id_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
v_id_5354_ = lean_ctor_get(v_ext_5351_, 0);
v___x_5355_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_5356_ = lean_array_get_borrowed(v___x_5355_, v_extensions_5352_, v_id_5354_);
lean_inc(v___x_5356_);
v___x_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5356_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_5358_, lean_object* v_extensions_5359_, lean_object* v_a_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5358_, v_extensions_5359_);
lean_dec_ref(v_extensions_5359_);
lean_dec_ref(v_ext_5358_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_5362_, lean_object* v_ext_5363_, lean_object* v_extensions_5364_){
_start:
{
lean_object* v___x_5366_; 
v___x_5366_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5363_, v_extensions_5364_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_5367_, lean_object* v_ext_5368_, lean_object* v_extensions_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_5367_, v_ext_5368_, v_extensions_5369_);
lean_dec_ref(v_extensions_5369_);
lean_dec_ref(v_ext_5368_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v___x_5376_; lean_object* v_extensions_5377_; lean_object* v_ref_5378_; lean_object* v___x_5379_; 
v___x_5376_ = lean_st_ref_get(v_a_5373_);
v_extensions_5377_ = lean_ctor_get(v___x_5376_, 9);
lean_inc_ref(v_extensions_5377_);
lean_dec(v___x_5376_);
v_ref_5378_ = lean_ctor_get(v_a_5374_, 2);
v___x_5379_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5372_, v_extensions_5377_);
lean_dec_ref(v_extensions_5377_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5387_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5382_ = v___x_5379_;
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5379_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5385_; 
if (v_isShared_5383_ == 0)
{
v___x_5385_ = v___x_5382_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
v___x_5385_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
return v___x_5385_;
}
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5399_; 
v_a_5388_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5399_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5390_ = v___x_5379_;
v_isShared_5391_ = v_isSharedCheck_5399_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5379_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5399_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5397_; 
v___x_5392_ = lean_io_error_to_string(v_a_5388_);
v___x_5393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5392_);
v___x_5394_ = l_Lean_MessageData_ofFormat(v___x_5393_);
lean_inc(v_ref_5378_);
v___x_5395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5395_, 0, v_ref_5378_);
lean_ctor_set(v___x_5395_, 1, v___x_5394_);
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 0, v___x_5395_);
v___x_5397_ = v___x_5390_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5395_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5400_, v_a_5401_, v_a_5402_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec_ref(v_ext_5400_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_5405_, lean_object* v_ext_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_){
_start:
{
lean_object* v___x_5414_; 
v___x_5414_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5406_, v_a_5408_, v_a_5411_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_5415_, lean_object* v_ext_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_5415_, v_ext_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec_ref(v_ext_5416_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_5425_, lean_object* v_f_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v___x_5429_; lean_object* v_share_5430_; lean_object* v_maxFVar_5431_; lean_object* v_proofInstInfo_5432_; lean_object* v_proofInstInfoFVar_5433_; lean_object* v_letValue_5434_; lean_object* v_inferType_5435_; lean_object* v_getLevel_5436_; lean_object* v_congrInfo_5437_; lean_object* v_defEqI_5438_; lean_object* v_extensions_5439_; lean_object* v_issues_5440_; lean_object* v_canon_5441_; lean_object* v_instanceOverrides_5442_; uint8_t v_debug_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5462_; 
v___x_5429_ = lean_st_ref_take(v_a_5427_);
v_share_5430_ = lean_ctor_get(v___x_5429_, 0);
v_maxFVar_5431_ = lean_ctor_get(v___x_5429_, 1);
v_proofInstInfo_5432_ = lean_ctor_get(v___x_5429_, 2);
v_proofInstInfoFVar_5433_ = lean_ctor_get(v___x_5429_, 3);
v_letValue_5434_ = lean_ctor_get(v___x_5429_, 4);
v_inferType_5435_ = lean_ctor_get(v___x_5429_, 5);
v_getLevel_5436_ = lean_ctor_get(v___x_5429_, 6);
v_congrInfo_5437_ = lean_ctor_get(v___x_5429_, 7);
v_defEqI_5438_ = lean_ctor_get(v___x_5429_, 8);
v_extensions_5439_ = lean_ctor_get(v___x_5429_, 9);
v_issues_5440_ = lean_ctor_get(v___x_5429_, 10);
v_canon_5441_ = lean_ctor_get(v___x_5429_, 11);
v_instanceOverrides_5442_ = lean_ctor_get(v___x_5429_, 12);
v_debug_5443_ = lean_ctor_get_uint8(v___x_5429_, sizeof(void*)*13);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5445_ = v___x_5429_;
v_isShared_5446_ = v_isSharedCheck_5462_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_instanceOverrides_5442_);
lean_inc(v_canon_5441_);
lean_inc(v_issues_5440_);
lean_inc(v_extensions_5439_);
lean_inc(v_defEqI_5438_);
lean_inc(v_congrInfo_5437_);
lean_inc(v_getLevel_5436_);
lean_inc(v_inferType_5435_);
lean_inc(v_letValue_5434_);
lean_inc(v_proofInstInfoFVar_5433_);
lean_inc(v_proofInstInfo_5432_);
lean_inc(v_maxFVar_5431_);
lean_inc(v_share_5430_);
lean_dec(v___x_5429_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5462_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v_id_5447_; lean_object* v___x_5448_; lean_object* v___y_5450_; lean_object* v___x_5456_; uint8_t v___x_5457_; 
v_id_5447_ = lean_ctor_get(v_ext_5425_, 0);
v___x_5448_ = lean_box(0);
v___x_5456_ = lean_array_get_size(v_extensions_5439_);
v___x_5457_ = lean_nat_dec_lt(v_id_5447_, v___x_5456_);
if (v___x_5457_ == 0)
{
lean_dec(v_f_5426_);
v___y_5450_ = v_extensions_5439_;
goto v___jp_5449_;
}
else
{
lean_object* v_v_5458_; lean_object* v_xs_x27_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v_v_5458_ = lean_array_fget(v_extensions_5439_, v_id_5447_);
v_xs_x27_5459_ = lean_array_fset(v_extensions_5439_, v_id_5447_, v___x_5448_);
v___x_5460_ = lean_apply_1(v_f_5426_, v_v_5458_);
v___x_5461_ = lean_array_fset(v_xs_x27_5459_, v_id_5447_, v___x_5460_);
v___y_5450_ = v___x_5461_;
goto v___jp_5449_;
}
v___jp_5449_:
{
lean_object* v___x_5452_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 9, v___y_5450_);
v___x_5452_ = v___x_5445_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_share_5430_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v_maxFVar_5431_);
lean_ctor_set(v_reuseFailAlloc_5455_, 2, v_proofInstInfo_5432_);
lean_ctor_set(v_reuseFailAlloc_5455_, 3, v_proofInstInfoFVar_5433_);
lean_ctor_set(v_reuseFailAlloc_5455_, 4, v_letValue_5434_);
lean_ctor_set(v_reuseFailAlloc_5455_, 5, v_inferType_5435_);
lean_ctor_set(v_reuseFailAlloc_5455_, 6, v_getLevel_5436_);
lean_ctor_set(v_reuseFailAlloc_5455_, 7, v_congrInfo_5437_);
lean_ctor_set(v_reuseFailAlloc_5455_, 8, v_defEqI_5438_);
lean_ctor_set(v_reuseFailAlloc_5455_, 9, v___y_5450_);
lean_ctor_set(v_reuseFailAlloc_5455_, 10, v_issues_5440_);
lean_ctor_set(v_reuseFailAlloc_5455_, 11, v_canon_5441_);
lean_ctor_set(v_reuseFailAlloc_5455_, 12, v_instanceOverrides_5442_);
lean_ctor_set_uint8(v_reuseFailAlloc_5455_, sizeof(void*)*13, v_debug_5443_);
v___x_5452_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = lean_st_ref_put(v_a_5427_, v___x_5452_);
v___x_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5448_);
return v___x_5454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_5463_, lean_object* v_f_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5463_, v_f_5464_, v_a_5465_);
lean_dec(v_a_5465_);
lean_dec_ref(v_ext_5463_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_5468_, lean_object* v_ext_5469_, lean_object* v_f_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_){
_start:
{
lean_object* v___x_5478_; 
v___x_5478_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5469_, v_f_5470_, v_a_5472_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5479_, lean_object* v_ext_5480_, lean_object* v_f_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5479_, v_ext_5480_, v_f_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_);
lean_dec(v_a_5487_);
lean_dec_ref(v_a_5486_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
lean_dec_ref(v_a_5482_);
lean_dec_ref(v_ext_5480_);
return v_res_5489_;
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
