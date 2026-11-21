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
case 2:
{
lean_object* v_rewritable_264_; lean_object* v___x_265_; 
v_rewritable_264_ = lean_ctor_get(v_t_259_, 0);
lean_inc_ref(v_rewritable_264_);
lean_dec_ref_known(v_t_259_, 1);
v___x_265_ = lean_apply_1(v_k_260_, v_rewritable_264_);
return v___x_265_;
}
default: 
{
lean_object* v_thm_266_; lean_object* v_rhsVarMask_267_; lean_object* v___x_268_; 
v_thm_266_ = lean_ctor_get(v_t_259_, 0);
lean_inc_ref(v_thm_266_);
v_rhsVarMask_267_ = lean_ctor_get(v_t_259_, 1);
lean_inc(v_rhsVarMask_267_);
lean_dec_ref_known(v_t_259_, 2);
v___x_268_ = lean_apply_2(v_k_260_, v_thm_266_, v_rhsVarMask_267_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_269_, lean_object* v_ctorIdx_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_271_, v_k_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_275_, lean_object* v_ctorIdx_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_k_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_275_, v_ctorIdx_276_, v_t_277_, v_h_278_, v_k_279_);
lean_dec(v_ctorIdx_276_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_281_, lean_object* v_none_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_281_, v_none_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_none_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_285_, v_none_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_289_, lean_object* v_fixedPrefix_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_289_, v_fixedPrefix_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_fixedPrefix_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_293_, v_fixedPrefix_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_297_, lean_object* v_interlaced_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_297_, v_interlaced_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_interlaced_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_301_, v_interlaced_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_305_, lean_object* v_congrTheorem_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_305_, v_congrTheorem_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_congrTheorem_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_309_, v_congrTheorem_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Expr_getAppFn(v_e_319_);
if (lean_obj_tag(v___x_325_) == 4)
{
lean_object* v_declName_326_; lean_object* v___x_327_; lean_object* v_env_328_; uint8_t v___x_329_; 
v_declName_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_declName_326_);
lean_dec_ref_known(v___x_325_, 2);
v___x_327_ = lean_st_ref_get(v_a_323_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
v___x_329_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_328_, v_declName_326_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_e_319_);
v___x_330_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; lean_object* v___x_333_; 
v___x_332_ = 0;
v___x_333_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_319_, v___x_332_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_353_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_353_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
if (lean_obj_tag(v_a_334_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v_val_338_ = lean_ctor_get(v_a_334_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_348_ == 0)
{
v___x_340_ = v_a_334_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v_a_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_val_338_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_343_);
v___x_345_ = v___x_336_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_351_; 
lean_dec(v_a_334_);
v___x_349_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_349_);
v___x_351_ = v___x_336_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
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
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_a_354_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_333_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_333_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec_ref(v___x_325_);
lean_dec_ref(v_e_319_);
v___x_362_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_371_, lean_object* v_e_372_){
_start:
{
if (lean_obj_tag(v_e_372_) == 4)
{
lean_object* v_declName_373_; uint8_t v___x_374_; 
v_declName_373_ = lean_ctor_get(v_e_372_, 0);
lean_inc(v_declName_373_);
lean_dec_ref_known(v_e_372_, 2);
v___x_374_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_371_, v_declName_373_);
return v___x_374_;
}
else
{
uint8_t v___x_375_; 
lean_dec_ref(v_e_372_);
lean_dec_ref(v_env_371_);
v___x_375_ = 0;
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_376_, lean_object* v_e_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_376_, v_e_377_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v___f_385_; lean_object* v___x_386_; 
v___x_383_ = lean_st_ref_get(v_a_381_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_385_, 0, v_env_384_);
v___x_386_ = lean_find_expr(v___f_385_, v_e_380_);
lean_dec_ref(v___f_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = 0;
v___x_388_ = lean_box(v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_398_; 
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_399_);
v___x_391_ = v___x_386_;
v_isShared_392_ = v_isSharedCheck_398_;
goto v_resetjp_390_;
}
else
{
lean_dec(v___x_386_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_398_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = 1;
v___x_394_ = lean_box(v___x_393_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 0);
lean_ctor_set(v___x_391_, 0, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_e_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_404_, v_a_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec_ref(v_e_409_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_e_414_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_429_, lean_object* v_x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_apply_1(v_x_430_, lean_box(0));
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_438_, lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_438_, v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 0;
return v___x_448_;
}
else
{
lean_object* v_key_449_; lean_object* v_tail_450_; uint8_t v___x_451_; 
v_key_449_ = lean_ctor_get(v_x_447_, 0);
v_tail_450_ = lean_ctor_get(v_x_447_, 2);
v___x_451_ = l_Lean_ExprStructEq_beq(v_key_449_, v_a_446_);
if (v___x_451_ == 0)
{
v_x_447_ = v_tail_450_;
goto _start;
}
else
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_453_, v_x_454_);
lean_dec(v_x_454_);
lean_dec_ref(v_a_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
return v_x_457_;
}
else
{
lean_object* v_key_459_; lean_object* v_value_460_; lean_object* v_tail_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_484_; 
v_key_459_ = lean_ctor_get(v_x_458_, 0);
v_value_460_ = lean_ctor_get(v_x_458_, 1);
v_tail_461_ = lean_ctor_get(v_x_458_, 2);
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_458_);
if (v_isSharedCheck_484_ == 0)
{
v___x_463_ = v_x_458_;
v_isShared_464_ = v_isSharedCheck_484_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_tail_461_);
lean_inc(v_value_460_);
lean_inc(v_key_459_);
lean_dec(v_x_458_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_484_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v_fold_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_465_ = lean_array_get_size(v_x_457_);
v___x_466_ = l_Lean_ExprStructEq_hash(v_key_459_);
v___x_467_ = 32ULL;
v___x_468_ = lean_uint64_shift_right(v___x_466_, v___x_467_);
v_fold_469_ = lean_uint64_xor(v___x_466_, v___x_468_);
v___x_470_ = 16ULL;
v___x_471_ = lean_uint64_shift_right(v_fold_469_, v___x_470_);
v___x_472_ = lean_uint64_xor(v_fold_469_, v___x_471_);
v___x_473_ = lean_uint64_to_usize(v___x_472_);
v___x_474_ = lean_usize_of_nat(v___x_465_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_usize_land(v___x_473_, v___x_476_);
v___x_478_ = lean_array_uget_borrowed(v_x_457_, v___x_477_);
lean_inc(v___x_478_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 2, v___x_478_);
v___x_480_ = v___x_463_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_key_459_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_value_460_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v___x_478_);
v___x_480_ = v_reuseFailAlloc_483_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; 
v___x_481_ = lean_array_uset(v_x_457_, v___x_477_, v___x_480_);
v_x_457_ = v___x_481_;
v_x_458_ = v_tail_461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_485_, lean_object* v_source_486_, lean_object* v_target_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_array_get_size(v_source_486_);
v___x_489_ = lean_nat_dec_lt(v_i_485_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec_ref(v_source_486_);
lean_dec(v_i_485_);
return v_target_487_;
}
else
{
lean_object* v_es_490_; lean_object* v___x_491_; lean_object* v_source_492_; lean_object* v_target_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_es_490_ = lean_array_fget(v_source_486_, v_i_485_);
v___x_491_ = lean_box(0);
v_source_492_ = lean_array_fset(v_source_486_, v_i_485_, v___x_491_);
v_target_493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_487_, v_es_490_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_i_485_, v___x_494_);
lean_dec(v_i_485_);
v_i_485_ = v___x_495_;
v_source_486_ = v_source_492_;
v_target_487_ = v_target_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_nbuckets_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_498_ = lean_array_get_size(v_data_497_);
v___x_499_ = lean_unsigned_to_nat(2u);
v_nbuckets_500_ = lean_nat_mul(v___x_498_, v___x_499_);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_box(0);
v___x_503_ = lean_mk_array(v_nbuckets_500_, v___x_502_);
v___x_504_ = lean_array_propagate_mark(v_data_497_, v___x_503_);
v___x_505_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_501_, v_data_497_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_506_, lean_object* v_b_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_dec(v_b_507_);
lean_dec_ref(v_a_506_);
return v_x_508_;
}
else
{
lean_object* v_key_509_; lean_object* v_value_510_; lean_object* v_tail_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_523_; 
v_key_509_ = lean_ctor_get(v_x_508_, 0);
v_value_510_ = lean_ctor_get(v_x_508_, 1);
v_tail_511_ = lean_ctor_get(v_x_508_, 2);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_523_ == 0)
{
v___x_513_ = v_x_508_;
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_tail_511_);
lean_inc(v_value_510_);
lean_inc(v_key_509_);
lean_dec(v_x_508_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_ExprStructEq_beq(v_key_509_, v_a_506_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_506_, v_b_507_, v_tail_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 2, v___x_516_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_key_509_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_value_510_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v___x_521_; 
lean_dec(v_value_510_);
lean_dec(v_key_509_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_b_507_);
lean_ctor_set(v___x_513_, 0, v_a_506_);
v___x_521_ = v___x_513_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_506_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_b_507_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_tail_511_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_524_, lean_object* v_a_525_, lean_object* v_b_526_){
_start:
{
lean_object* v_size_527_; lean_object* v_buckets_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_571_; 
v_size_527_ = lean_ctor_get(v_m_524_, 0);
v_buckets_528_ = lean_ctor_get(v_m_524_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_m_524_);
if (v_isSharedCheck_571_ == 0)
{
v___x_530_ = v_m_524_;
v_isShared_531_ = v_isSharedCheck_571_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_buckets_528_);
lean_inc(v_size_527_);
lean_dec(v_m_524_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_571_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v_fold_536_; uint64_t v___x_537_; uint64_t v___x_538_; uint64_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v_bkt_545_; uint8_t v___x_546_; 
v___x_532_ = lean_array_get_size(v_buckets_528_);
v___x_533_ = l_Lean_ExprStructEq_hash(v_a_525_);
v___x_534_ = 32ULL;
v___x_535_ = lean_uint64_shift_right(v___x_533_, v___x_534_);
v_fold_536_ = lean_uint64_xor(v___x_533_, v___x_535_);
v___x_537_ = 16ULL;
v___x_538_ = lean_uint64_shift_right(v_fold_536_, v___x_537_);
v___x_539_ = lean_uint64_xor(v_fold_536_, v___x_538_);
v___x_540_ = lean_uint64_to_usize(v___x_539_);
v___x_541_ = lean_usize_of_nat(v___x_532_);
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_sub(v___x_541_, v___x_542_);
v___x_544_ = lean_usize_land(v___x_540_, v___x_543_);
v_bkt_545_ = lean_array_uget_borrowed(v_buckets_528_, v___x_544_);
v___x_546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_525_, v_bkt_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v_size_x27_548_; lean_object* v___x_549_; lean_object* v_buckets_x27_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v_size_x27_548_ = lean_nat_add(v_size_527_, v___x_547_);
lean_dec(v_size_527_);
lean_inc(v_bkt_545_);
v___x_549_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_549_, 0, v_a_525_);
lean_ctor_set(v___x_549_, 1, v_b_526_);
lean_ctor_set(v___x_549_, 2, v_bkt_545_);
v_buckets_x27_550_ = lean_array_uset(v_buckets_528_, v___x_544_, v___x_549_);
v___x_551_ = lean_unsigned_to_nat(4u);
v___x_552_ = lean_nat_mul(v_size_x27_548_, v___x_551_);
v___x_553_ = lean_unsigned_to_nat(3u);
v___x_554_ = lean_nat_div(v___x_552_, v___x_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_array_get_size(v_buckets_x27_550_);
v___x_556_ = lean_nat_dec_le(v___x_554_, v___x_555_);
lean_dec(v___x_554_);
if (v___x_556_ == 0)
{
lean_object* v_val_557_; lean_object* v___x_559_; 
v_val_557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_550_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_val_557_);
lean_ctor_set(v___x_530_, 0, v_size_x27_548_);
v___x_559_ = v___x_530_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_size_x27_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_val_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_562_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_buckets_x27_550_);
lean_ctor_set(v___x_530_, 0, v_size_x27_548_);
v___x_562_ = v___x_530_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_size_x27_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_buckets_x27_550_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v___x_564_; lean_object* v_buckets_x27_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
lean_inc(v_bkt_545_);
v___x_564_ = lean_box(0);
v_buckets_x27_565_ = lean_array_uset(v_buckets_528_, v___x_544_, v___x_564_);
v___x_566_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_525_, v_b_526_, v_bkt_545_);
v___x_567_ = lean_array_uset(v_buckets_x27_565_, v___x_544_, v___x_566_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v___x_567_);
v___x_569_ = v___x_530_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_size_527_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_572_, lean_object* v_e_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_st_ref_take(v_a_572_);
v___x_577_ = lean_box(0);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_576_, v_e_573_, v_a_574_);
v___x_579_ = lean_st_ref_put(v_a_572_, v___x_578_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_580_, lean_object* v_e_581_, lean_object* v_a_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_580_, v_e_581_, v_a_582_);
lean_dec(v_a_580_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = l_Lean_maxRecDepthErrorMessage;
v___x_591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_593_ = l_Lean_MessageData_ofFormat(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_595_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_596_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_ref_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___y_613_; lean_object* v_toCold_622_; lean_object* v_currRecDepth_623_; lean_object* v_ref_624_; uint16_t v_optionFlags_625_; uint8_t v_suppressElabErrors_626_; uint8_t v_checkDeprecated_627_; uint8_t v_isRecordingDeps_628_; lean_object* v_maxRecDepth_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_toCold_622_ = lean_ctor_get(v___y_609_, 0);
v_currRecDepth_623_ = lean_ctor_get(v___y_609_, 1);
v_ref_624_ = lean_ctor_get(v___y_609_, 2);
v_optionFlags_625_ = lean_ctor_get_uint16(v___y_609_, sizeof(void*)*3);
v_suppressElabErrors_626_ = lean_ctor_get_uint8(v___y_609_, sizeof(void*)*3 + 2);
v_checkDeprecated_627_ = lean_ctor_get_uint8(v___y_609_, sizeof(void*)*3 + 3);
v_isRecordingDeps_628_ = lean_ctor_get_uint8(v___y_609_, sizeof(void*)*3 + 4);
v_maxRecDepth_634_ = lean_ctor_get(v_toCold_622_, 3);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_nat_dec_eq(v_maxRecDepth_634_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_eq(v_currRecDepth_623_, v_maxRecDepth_634_);
if (v___x_637_ == 0)
{
goto v___jp_629_;
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v_x_605_);
lean_inc(v_ref_624_);
v___x_638_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_624_);
v___y_613_ = v___x_638_;
goto v___jp_612_;
}
}
else
{
goto v___jp_629_;
}
v___jp_612_:
{
if (lean_obj_tag(v___y_613_) == 0)
{
return v___y_613_;
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___y_613_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___y_613_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___y_613_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___y_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
v___jp_629_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_currRecDepth_623_, v___x_630_);
lean_inc(v_ref_624_);
lean_inc_ref(v_toCold_622_);
v___x_632_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_632_, 0, v_toCold_622_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_ctor_set(v___x_632_, 2, v_ref_624_);
lean_ctor_set_uint16(v___x_632_, sizeof(void*)*3, v_optionFlags_625_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 2, v_suppressElabErrors_626_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 3, v_checkDeprecated_627_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 4, v_isRecordingDeps_628_);
lean_inc(v___y_610_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
v___x_633_ = lean_apply_6(v_x_605_, v___y_606_, v___y_607_, v___y_608_, v___x_632_, v___y_610_, lean_box(0));
v___y_613_ = v___x_633_;
goto v___jp_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_647_, lean_object* v_x_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_apply_1(v_x_648_, lean_box(0));
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_656_, v_x_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v_key_667_; lean_object* v_value_668_; lean_object* v_tail_669_; uint8_t v___x_670_; 
v_key_667_ = lean_ctor_get(v_x_665_, 0);
v_value_668_ = lean_ctor_get(v_x_665_, 1);
v_tail_669_ = lean_ctor_get(v_x_665_, 2);
v___x_670_ = l_Lean_ExprStructEq_beq(v_key_667_, v_a_664_);
if (v___x_670_ == 0)
{
v_x_665_ = v_tail_669_;
goto _start;
}
else
{
lean_object* v___x_672_; 
lean_inc(v_value_668_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v_value_668_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_673_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_a_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_buckets_678_; lean_object* v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v_fold_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_buckets_678_ = lean_ctor_get(v_m_676_, 1);
v___x_679_ = lean_array_get_size(v_buckets_678_);
v___x_680_ = l_Lean_ExprStructEq_hash(v_a_677_);
v___x_681_ = 32ULL;
v___x_682_ = lean_uint64_shift_right(v___x_680_, v___x_681_);
v_fold_683_ = lean_uint64_xor(v___x_680_, v___x_682_);
v___x_684_ = 16ULL;
v___x_685_ = lean_uint64_shift_right(v_fold_683_, v___x_684_);
v___x_686_ = lean_uint64_xor(v_fold_683_, v___x_685_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = lean_usize_of_nat(v___x_679_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_sub(v___x_688_, v___x_689_);
v___x_691_ = lean_usize_land(v___x_687_, v___x_690_);
v___x_692_ = lean_array_uget_borrowed(v_buckets_678_, v___x_691_);
v___x_693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_677_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_694_, v_a_695_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_m_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_697_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_711_, lean_object* v___y_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc(v___y_712_);
v___x_719_ = lean_apply_7(v_k_711_, v_b_713_, v___y_712_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, lean_box(0));
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_720_, lean_object* v___y_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_720_, v___y_721_, v_b_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_729_, uint8_t v_bi_730_, lean_object* v_type_731_, lean_object* v_k_732_, uint8_t v_kind_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___f_740_; lean_object* v___x_741_; 
lean_inc(v___y_734_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_740_, 0, v_k_732_);
lean_closure_set(v___f_740_, 1, v___y_734_);
v___x_741_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_729_, v_bi_730_, v_type_731_, v___f_740_, v_kind_733_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_741_) == 0)
{
return v___x_741_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_750_, lean_object* v_bi_751_, lean_object* v_type_752_, lean_object* v_k_753_, lean_object* v_kind_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_bi_boxed_761_; uint8_t v_kind_boxed_762_; lean_object* v_res_763_; 
v_bi_boxed_761_ = lean_unbox(v_bi_751_);
v_kind_boxed_762_ = lean_unbox(v_kind_754_);
v_res_763_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_750_, v_bi_boxed_761_, v_type_752_, v_k_753_, v_kind_boxed_762_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_764_, lean_object* v_type_765_, lean_object* v_val_766_, lean_object* v_k_767_, uint8_t v_nondep_768_, uint8_t v_kind_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; 
lean_inc(v___y_770_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_776_, 0, v_k_767_);
lean_closure_set(v___f_776_, 1, v___y_770_);
v___x_777_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_764_, v_type_765_, v_val_766_, v___f_776_, v_nondep_768_, v_kind_769_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_777_) == 0)
{
return v___x_777_;
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_786_, lean_object* v_type_787_, lean_object* v_val_788_, lean_object* v_k_789_, lean_object* v_nondep_790_, lean_object* v_kind_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_nondep_boxed_798_; uint8_t v_kind_boxed_799_; lean_object* v_res_800_; 
v_nondep_boxed_798_ = lean_unbox(v_nondep_790_);
v_kind_boxed_799_ = lean_unbox(v_kind_791_);
v_res_800_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_786_, v_type_787_, v_val_788_, v_k_789_, v_nondep_boxed_798_, v_kind_boxed_799_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_801_, lean_object* v_pre_802_, lean_object* v_post_803_, lean_object* v_usedLetOnly_804_, lean_object* v_skipConstInApp_805_, lean_object* v_skipInstances_806_, lean_object* v_body_807_, lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_usedLetOnly_boxed_815_; uint8_t v_skipConstInApp_boxed_816_; uint8_t v_skipInstances_boxed_817_; lean_object* v_res_818_; 
v_usedLetOnly_boxed_815_ = lean_unbox(v_usedLetOnly_804_);
v_skipConstInApp_boxed_816_ = lean_unbox(v_skipConstInApp_805_);
v_skipInstances_boxed_817_ = lean_unbox(v_skipInstances_806_);
v_res_818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_801_, v_pre_802_, v_post_803_, v_usedLetOnly_boxed_815_, v_skipConstInApp_boxed_816_, v_skipInstances_boxed_817_, v_body_807_, v_x_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_822_, lean_object* v_pre_823_, lean_object* v_post_824_, uint8_t v_usedLetOnly_825_, uint8_t v_skipConstInApp_826_, uint8_t v_skipInstances_827_, lean_object* v_body_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_array_push(v_fvars_822_, v_x_829_);
v___x_837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_823_, v_post_824_, v_usedLetOnly_825_, v_skipConstInApp_826_, v_skipInstances_827_, v___x_836_, v_body_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_838_, lean_object* v_pre_839_, lean_object* v_post_840_, lean_object* v_usedLetOnly_841_, lean_object* v_skipConstInApp_842_, lean_object* v_skipInstances_843_, lean_object* v_body_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v_usedLetOnly_boxed_852_; uint8_t v_skipConstInApp_boxed_853_; uint8_t v_skipInstances_boxed_854_; lean_object* v_res_855_; 
v_usedLetOnly_boxed_852_ = lean_unbox(v_usedLetOnly_841_);
v_skipConstInApp_boxed_853_ = lean_unbox(v_skipConstInApp_842_);
v_skipInstances_boxed_854_ = lean_unbox(v_skipInstances_843_);
v_res_855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_838_, v_pre_839_, v_post_840_, v_usedLetOnly_boxed_852_, v_skipConstInApp_boxed_853_, v_skipInstances_boxed_854_, v_body_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_856_, lean_object* v_post_857_, uint8_t v_usedLetOnly_858_, uint8_t v_skipConstInApp_859_, uint8_t v_skipInstances_860_, lean_object* v_e_861_, lean_object* v_a_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
lean_inc_ref(v_post_857_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
lean_inc_ref(v_e_861_);
v___x_868_ = lean_apply_6(v_post_857_, v_e_861_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_887_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_887_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_887_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_887_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
switch(lean_obj_tag(v_a_869_))
{
case 0:
{
lean_object* v_e_873_; lean_object* v___x_875_; 
lean_dec_ref(v_e_861_);
lean_dec_ref(v_post_857_);
lean_dec_ref(v_pre_856_);
v_e_873_ = lean_ctor_get(v_a_869_, 0);
lean_inc_ref(v_e_873_);
lean_dec_ref_known(v_a_869_, 1);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_e_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_e_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
case 1:
{
lean_object* v_e_877_; lean_object* v___x_878_; 
lean_del_object(v___x_871_);
lean_dec_ref(v_e_861_);
v_e_877_ = lean_ctor_get(v_a_869_, 0);
lean_inc_ref(v_e_877_);
lean_dec_ref_known(v_a_869_, 1);
v___x_878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_856_, v_post_857_, v_usedLetOnly_858_, v_skipConstInApp_859_, v_skipInstances_860_, v_e_877_, v_a_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
return v___x_878_;
}
default: 
{
lean_object* v_e_x3f_879_; 
lean_dec_ref(v_post_857_);
lean_dec_ref(v_pre_856_);
v_e_x3f_879_ = lean_ctor_get(v_a_869_, 0);
lean_inc(v_e_x3f_879_);
lean_dec_ref_known(v_a_869_, 1);
if (lean_obj_tag(v_e_x3f_879_) == 0)
{
lean_object* v___x_881_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_e_861_);
v___x_881_ = v___x_871_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_e_861_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v_val_883_; lean_object* v___x_885_; 
lean_dec_ref(v_e_861_);
v_val_883_ = lean_ctor_get(v_e_x3f_879_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v_e_x3f_879_, 1);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_val_883_);
v___x_885_ = v___x_871_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_val_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_e_861_);
lean_dec_ref(v_post_857_);
lean_dec_ref(v_pre_856_);
v_a_888_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_868_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_868_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_896_, lean_object* v_post_897_, uint8_t v_usedLetOnly_898_, uint8_t v_skipConstInApp_899_, uint8_t v_skipInstances_900_, lean_object* v_fvars_901_, lean_object* v_e_902_, lean_object* v_a_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
if (lean_obj_tag(v_e_902_) == 6)
{
lean_object* v_binderName_909_; lean_object* v_binderType_910_; lean_object* v_body_911_; uint8_t v_binderInfo_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_binderName_909_ = lean_ctor_get(v_e_902_, 0);
lean_inc(v_binderName_909_);
v_binderType_910_ = lean_ctor_get(v_e_902_, 1);
lean_inc_ref(v_binderType_910_);
v_body_911_ = lean_ctor_get(v_e_902_, 2);
lean_inc_ref(v_body_911_);
v_binderInfo_912_ = lean_ctor_get_uint8(v_e_902_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_902_, 3);
v___x_913_ = lean_box(v_usedLetOnly_898_);
v___x_914_ = lean_box(v_skipConstInApp_899_);
v___x_915_ = lean_box(v_skipInstances_900_);
lean_inc_ref(v_post_897_);
lean_inc_ref(v_pre_896_);
lean_inc_ref(v_fvars_901_);
v___f_916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_916_, 0, v_fvars_901_);
lean_closure_set(v___f_916_, 1, v_pre_896_);
lean_closure_set(v___f_916_, 2, v_post_897_);
lean_closure_set(v___f_916_, 3, v___x_913_);
lean_closure_set(v___f_916_, 4, v___x_914_);
lean_closure_set(v___f_916_, 5, v___x_915_);
lean_closure_set(v___f_916_, 6, v_body_911_);
v___x_917_ = lean_expr_instantiate_rev(v_binderType_910_, v_fvars_901_);
lean_dec_ref(v_fvars_901_);
lean_dec_ref(v_binderType_910_);
v___x_918_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_896_, v_post_897_, v_usedLetOnly_898_, v_skipConstInApp_899_, v_skipInstances_900_, v___x_917_, v_a_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; uint8_t v___x_920_; lean_object* v___x_921_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = 0;
v___x_921_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_909_, v_binderInfo_912_, v_a_919_, v___f_916_, v___x_920_, v_a_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_921_;
}
else
{
lean_dec_ref(v___f_916_);
lean_dec(v_binderName_909_);
return v___x_918_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_expr_instantiate_rev(v_e_902_, v_fvars_901_);
lean_dec_ref(v_e_902_);
lean_inc_ref(v_post_897_);
lean_inc_ref(v_pre_896_);
v___x_923_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_896_, v_post_897_, v_usedLetOnly_898_, v_skipConstInApp_899_, v_skipInstances_900_, v___x_922_, v_a_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; uint8_t v___x_925_; uint8_t v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_925_ = 0;
v___x_926_ = 1;
v___x_927_ = 1;
v___x_928_ = l_Lean_Meta_mkLambdaFVars(v_fvars_901_, v_a_924_, v___x_925_, v_usedLetOnly_898_, v___x_925_, v___x_926_, v___x_927_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec_ref(v_fvars_901_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_896_, v_post_897_, v_usedLetOnly_898_, v_skipConstInApp_899_, v_skipInstances_900_, v_a_929_, v_a_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_930_;
}
else
{
lean_dec_ref(v_post_897_);
lean_dec_ref(v_pre_896_);
return v___x_928_;
}
}
else
{
lean_dec_ref(v_fvars_901_);
lean_dec_ref(v_post_897_);
lean_dec_ref(v_pre_896_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_931_, lean_object* v_pre_932_, lean_object* v_post_933_, uint8_t v_usedLetOnly_934_, uint8_t v_skipConstInApp_935_, uint8_t v_skipInstances_936_, lean_object* v_body_937_, lean_object* v_x_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_array_push(v_fvars_931_, v_x_938_);
v___x_946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_932_, v_post_933_, v_usedLetOnly_934_, v_skipConstInApp_935_, v_skipInstances_936_, v___x_945_, v_body_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_947_, lean_object* v_pre_948_, lean_object* v_post_949_, lean_object* v_usedLetOnly_950_, lean_object* v_skipConstInApp_951_, lean_object* v_skipInstances_952_, lean_object* v_body_953_, lean_object* v_x_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v_usedLetOnly_boxed_961_; uint8_t v_skipConstInApp_boxed_962_; uint8_t v_skipInstances_boxed_963_; lean_object* v_res_964_; 
v_usedLetOnly_boxed_961_ = lean_unbox(v_usedLetOnly_950_);
v_skipConstInApp_boxed_962_ = lean_unbox(v_skipConstInApp_951_);
v_skipInstances_boxed_963_ = lean_unbox(v_skipInstances_952_);
v_res_964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_947_, v_pre_948_, v_post_949_, v_usedLetOnly_boxed_961_, v_skipConstInApp_boxed_962_, v_skipInstances_boxed_963_, v_body_953_, v_x_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_965_, lean_object* v_post_966_, uint8_t v_usedLetOnly_967_, uint8_t v_skipConstInApp_968_, uint8_t v_skipInstances_969_, lean_object* v_fvars_970_, lean_object* v_e_971_, lean_object* v_a_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
if (lean_obj_tag(v_e_971_) == 8)
{
lean_object* v_declName_978_; lean_object* v_type_979_; lean_object* v_value_980_; lean_object* v_body_981_; uint8_t v_nondep_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___f_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_declName_978_ = lean_ctor_get(v_e_971_, 0);
lean_inc(v_declName_978_);
v_type_979_ = lean_ctor_get(v_e_971_, 1);
lean_inc_ref(v_type_979_);
v_value_980_ = lean_ctor_get(v_e_971_, 2);
lean_inc_ref(v_value_980_);
v_body_981_ = lean_ctor_get(v_e_971_, 3);
lean_inc_ref(v_body_981_);
v_nondep_982_ = lean_ctor_get_uint8(v_e_971_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_971_, 4);
v___x_983_ = lean_box(v_usedLetOnly_967_);
v___x_984_ = lean_box(v_skipConstInApp_968_);
v___x_985_ = lean_box(v_skipInstances_969_);
lean_inc_ref_n(v_post_966_, 2);
lean_inc_ref_n(v_pre_965_, 2);
lean_inc_ref(v_fvars_970_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_986_, 0, v_fvars_970_);
lean_closure_set(v___f_986_, 1, v_pre_965_);
lean_closure_set(v___f_986_, 2, v_post_966_);
lean_closure_set(v___f_986_, 3, v___x_983_);
lean_closure_set(v___f_986_, 4, v___x_984_);
lean_closure_set(v___f_986_, 5, v___x_985_);
lean_closure_set(v___f_986_, 6, v_body_981_);
v___x_987_ = lean_expr_instantiate_rev(v_type_979_, v_fvars_970_);
lean_dec_ref(v_type_979_);
v___x_988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_965_, v_post_966_, v_usedLetOnly_967_, v_skipConstInApp_968_, v_skipInstances_969_, v___x_987_, v_a_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = lean_expr_instantiate_rev(v_value_980_, v_fvars_970_);
lean_dec_ref(v_fvars_970_);
lean_dec_ref(v_value_980_);
v___x_991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_965_, v_post_966_, v_usedLetOnly_967_, v_skipConstInApp_968_, v_skipInstances_969_, v___x_990_, v_a_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; uint8_t v___x_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = 0;
v___x_994_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_978_, v_a_989_, v_a_992_, v___f_986_, v_nondep_982_, v___x_993_, v_a_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_994_;
}
else
{
lean_dec(v_a_989_);
lean_dec_ref(v___f_986_);
lean_dec(v_declName_978_);
return v___x_991_;
}
}
else
{
lean_dec_ref(v___f_986_);
lean_dec_ref(v_value_980_);
lean_dec(v_declName_978_);
lean_dec_ref(v_fvars_970_);
lean_dec_ref(v_post_966_);
lean_dec_ref(v_pre_965_);
return v___x_988_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_expr_instantiate_rev(v_e_971_, v_fvars_970_);
lean_dec_ref(v_e_971_);
lean_inc_ref(v_post_966_);
lean_inc_ref(v_pre_965_);
v___x_996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_965_, v_post_966_, v_usedLetOnly_967_, v_skipConstInApp_968_, v_skipInstances_969_, v___x_995_, v_a_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; uint8_t v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = 0;
v___x_999_ = 1;
v___x_1000_ = l_Lean_Meta_mkLetFVars(v_fvars_970_, v_a_997_, v_usedLetOnly_967_, v___x_998_, v___x_999_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec_ref(v_fvars_970_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_965_, v_post_966_, v_usedLetOnly_967_, v_skipConstInApp_968_, v_skipInstances_969_, v_a_1001_, v_a_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_1002_;
}
else
{
lean_dec_ref(v_post_966_);
lean_dec_ref(v_pre_965_);
return v___x_1000_;
}
}
else
{
lean_dec_ref(v_fvars_970_);
lean_dec_ref(v_post_966_);
lean_dec_ref(v_pre_965_);
return v___x_996_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v_dummy_1004_; 
v___x_1003_ = lean_box(0);
v_dummy_1004_ = l_Lean_Expr_sort___override(v___x_1003_);
return v_dummy_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_1005_, lean_object* v_post_1006_, uint8_t v_usedLetOnly_1007_, uint8_t v_skipConstInApp_1008_, uint8_t v_skipInstances_1009_, size_t v_sz_1010_, size_t v_i_1011_, lean_object* v_bs_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_lt(v_i_1011_, v_sz_1010_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v_post_1006_);
lean_dec_ref(v_pre_1005_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_bs_1012_);
return v___x_1020_;
}
else
{
lean_object* v_v_1021_; lean_object* v___x_1022_; lean_object* v_bs_x27_1023_; lean_object* v___x_1024_; 
v_v_1021_ = lean_array_uget(v_bs_1012_, v_i_1011_);
v___x_1022_ = lean_unsigned_to_nat(0u);
v_bs_x27_1023_ = lean_array_uset(v_bs_1012_, v_i_1011_, v___x_1022_);
lean_inc_ref(v_post_1006_);
lean_inc_ref(v_pre_1005_);
v___x_1024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1005_, v_post_1006_, v_usedLetOnly_1007_, v_skipConstInApp_1008_, v_skipInstances_1009_, v_v_1021_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1011_, v___x_1026_);
v___x_1028_ = lean_array_uset(v_bs_x27_1023_, v_i_1011_, v_a_1025_);
v_i_1011_ = v___x_1027_;
v_bs_1012_ = v___x_1028_;
goto _start;
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v_bs_x27_1023_);
lean_dec_ref(v_post_1006_);
lean_dec_ref(v_pre_1005_);
v_a_1030_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1024_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1024_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1038_, lean_object* v_post_1039_, uint8_t v_usedLetOnly_1040_, uint8_t v_skipConstInApp_1041_, uint8_t v_skipInstances_1042_, lean_object* v___x_1043_, lean_object* v___y_1044_, lean_object* v_b_1045_, lean_object* v_a_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1038_, v_post_1039_, v_usedLetOnly_1040_, v_skipConstInApp_1041_, v_skipInstances_1042_, v___x_1043_, v___y_1044_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = lean_array_fset(v_b_1045_, v_a_1046_, v_a_1053_);
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_b_1045_);
v_a_1063_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1052_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1052_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1071_, lean_object* v_post_1072_, lean_object* v_usedLetOnly_1073_, lean_object* v_skipConstInApp_1074_, lean_object* v_skipInstances_1075_, lean_object* v___x_1076_, lean_object* v___y_1077_, lean_object* v_b_1078_, lean_object* v_a_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v_usedLetOnly_boxed_1085_; uint8_t v_skipConstInApp_boxed_1086_; uint8_t v_skipInstances_boxed_1087_; lean_object* v_res_1088_; 
v_usedLetOnly_boxed_1085_ = lean_unbox(v_usedLetOnly_1073_);
v_skipConstInApp_boxed_1086_ = lean_unbox(v_skipConstInApp_1074_);
v_skipInstances_boxed_1087_ = lean_unbox(v_skipInstances_1075_);
v_res_1088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1071_, v_post_1072_, v_usedLetOnly_boxed_1085_, v_skipConstInApp_boxed_1086_, v_skipInstances_boxed_1087_, v___x_1076_, v___y_1077_, v_b_1078_, v_a_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v_a_1079_);
lean_dec(v___y_1077_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1089_, lean_object* v___x_1090_, lean_object* v_pre_1091_, lean_object* v_post_1092_, uint8_t v_usedLetOnly_1093_, uint8_t v_skipConstInApp_1094_, uint8_t v_skipInstances_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___y_1105_; uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_lt(v_a_1096_, v_upperBound_1089_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec(v_a_1096_);
lean_dec_ref(v_post_1092_);
lean_dec_ref(v_pre_1091_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_b_1097_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = lean_array_fget_borrowed(v_b_1097_, v_a_1096_);
v___x_1131_ = lean_array_get_size(v___x_1090_);
v___x_1132_ = lean_nat_dec_lt(v_a_1096_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; 
lean_inc(v___x_1130_);
v___x_1133_ = lean_box(v_usedLetOnly_1093_);
v___x_1134_ = lean_box(v_skipConstInApp_1094_);
v___x_1135_ = lean_box(v_skipInstances_1095_);
lean_inc(v_a_1096_);
lean_inc(v___y_1098_);
lean_inc_ref(v_post_1092_);
lean_inc_ref(v_pre_1091_);
v___f_1136_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1136_, 0, v_pre_1091_);
lean_closure_set(v___f_1136_, 1, v_post_1092_);
lean_closure_set(v___f_1136_, 2, v___x_1133_);
lean_closure_set(v___f_1136_, 3, v___x_1134_);
lean_closure_set(v___f_1136_, 4, v___x_1135_);
lean_closure_set(v___f_1136_, 5, v___x_1130_);
lean_closure_set(v___f_1136_, 6, v___y_1098_);
lean_closure_set(v___f_1136_, 7, v_b_1097_);
lean_closure_set(v___f_1136_, 8, v_a_1096_);
v___y_1105_ = v___f_1136_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1137_; uint8_t v_isInstance_1138_; 
v___x_1137_ = lean_array_fget_borrowed(v___x_1090_, v_a_1096_);
v_isInstance_1138_ = lean_ctor_get_uint8(v___x_1137_, sizeof(void*)*1 + 4);
if (v_isInstance_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; 
lean_inc(v___x_1130_);
v___x_1139_ = lean_box(v_usedLetOnly_1093_);
v___x_1140_ = lean_box(v_skipConstInApp_1094_);
v___x_1141_ = lean_box(v_skipInstances_1095_);
lean_inc(v_a_1096_);
lean_inc(v___y_1098_);
lean_inc_ref(v_post_1092_);
lean_inc_ref(v_pre_1091_);
v___f_1142_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1142_, 0, v_pre_1091_);
lean_closure_set(v___f_1142_, 1, v_post_1092_);
lean_closure_set(v___f_1142_, 2, v___x_1139_);
lean_closure_set(v___f_1142_, 3, v___x_1140_);
lean_closure_set(v___f_1142_, 4, v___x_1141_);
lean_closure_set(v___f_1142_, 5, v___x_1130_);
lean_closure_set(v___f_1142_, 6, v___y_1098_);
lean_closure_set(v___f_1142_, 7, v_b_1097_);
lean_closure_set(v___f_1142_, 8, v_a_1096_);
v___y_1105_ = v___f_1142_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1143_; lean_object* v___f_1144_; 
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_b_1097_);
v___f_1144_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1144_, 0, v___x_1143_);
v___y_1105_ = v___f_1144_;
goto v___jp_1104_;
}
}
}
v___jp_1104_:
{
lean_object* v___x_1106_; 
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1099_);
v___x_1106_ = lean_apply_5(v___y_1105_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, lean_box(0));
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1119_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1119_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1119_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
if (lean_obj_tag(v_a_1107_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; 
lean_dec(v_a_1096_);
lean_dec_ref(v_post_1092_);
lean_dec_ref(v_pre_1091_);
v_a_1111_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v_a_1107_, 1);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_a_1111_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_del_object(v___x_1109_);
v_a_1115_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v_a_1107_, 1);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_a_1096_, v___x_1116_);
lean_dec(v_a_1096_);
v_a_1096_ = v___x_1117_;
v_b_1097_ = v_a_1115_;
goto _start;
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_a_1096_);
lean_dec_ref(v_post_1092_);
lean_dec_ref(v_pre_1091_);
v_a_1120_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1106_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1106_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1145_, lean_object* v_pre_1146_, lean_object* v_post_1147_, uint8_t v_usedLetOnly_1148_, uint8_t v_skipConstInApp_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_f_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; 
if (lean_obj_tag(v_x_1150_) == 5)
{
lean_object* v_fn_1208_; lean_object* v_arg_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_fn_1208_ = lean_ctor_get(v_x_1150_, 0);
lean_inc_ref(v_fn_1208_);
v_arg_1209_ = lean_ctor_get(v_x_1150_, 1);
lean_inc_ref(v_arg_1209_);
lean_dec_ref_known(v_x_1150_, 2);
v___x_1210_ = lean_array_set(v_x_1151_, v_x_1152_, v_arg_1209_);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_sub(v_x_1152_, v___x_1211_);
lean_dec(v_x_1152_);
v_x_1150_ = v_fn_1208_;
v_x_1151_ = v___x_1210_;
v_x_1152_ = v___x_1212_;
goto _start;
}
else
{
lean_dec(v_x_1152_);
if (v_skipConstInApp_1149_ == 0)
{
goto v___jp_1205_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = l_Lean_Expr_isConst(v_x_1150_);
if (v___x_1214_ == 0)
{
goto v___jp_1205_;
}
else
{
v_f_1160_ = v_x_1150_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___y_1154_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___y_1156_;
v___y_1165_ = v___y_1157_;
goto v___jp_1159_;
}
}
}
v___jp_1159_:
{
if (v_skipInstances_1145_ == 0)
{
size_t v_sz_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v_sz_1166_ = lean_array_size(v_x_1151_);
v___x_1167_ = ((size_t)0ULL);
lean_inc_ref(v_post_1147_);
lean_inc_ref(v_pre_1146_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1146_, v_post_1147_, v_usedLetOnly_1148_, v_skipConstInApp_1149_, v_skipInstances_1145_, v_sz_1166_, v___x_1167_, v_x_1151_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = l_Lean_mkAppN(v_f_1160_, v_a_1169_);
lean_dec(v_a_1169_);
v___x_1171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1146_, v_post_1147_, v_usedLetOnly_1148_, v_skipConstInApp_1149_, v_skipInstances_1145_, v___x_1170_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
return v___x_1171_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v_f_1160_);
lean_dec_ref(v_post_1147_);
lean_dec_ref(v_pre_1146_);
v_a_1172_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1168_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1168_);
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
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_x_1151_);
lean_inc_ref(v_f_1160_);
v___x_1181_ = l_Lean_Meta_getFunInfoNArgs(v_f_1160_, v___x_1180_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_paramInfo_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v_paramInfo_1183_ = lean_ctor_get(v_a_1182_, 0);
lean_inc_ref(v_paramInfo_1183_);
lean_dec(v_a_1182_);
v___x_1184_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1147_);
lean_inc_ref(v_pre_1146_);
v___x_1185_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1180_, v_paramInfo_1183_, v_pre_1146_, v_post_1147_, v_usedLetOnly_1148_, v_skipConstInApp_1149_, v_skipInstances_1145_, v___x_1184_, v_x_1151_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec_ref(v_paramInfo_1183_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l_Lean_mkAppN(v_f_1160_, v_a_1186_);
lean_dec(v_a_1186_);
v___x_1188_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1146_, v_post_1147_, v_usedLetOnly_1148_, v_skipConstInApp_1149_, v_skipInstances_1145_, v___x_1187_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_f_1160_);
lean_dec_ref(v_post_1147_);
lean_dec_ref(v_pre_1146_);
v_a_1189_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1185_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1185_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_f_1160_);
lean_dec_ref(v_x_1151_);
lean_dec_ref(v_post_1147_);
lean_dec_ref(v_pre_1146_);
v_a_1197_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1181_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1181_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
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
v___jp_1205_:
{
lean_object* v___x_1206_; 
lean_inc_ref(v_post_1147_);
lean_inc_ref(v_pre_1146_);
v___x_1206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1146_, v_post_1147_, v_usedLetOnly_1148_, v_skipConstInApp_1149_, v_skipInstances_1145_, v_x_1150_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v_f_1160_ = v_a_1207_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___y_1154_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___y_1156_;
v___y_1165_ = v___y_1157_;
goto v___jp_1159_;
}
else
{
lean_dec_ref(v_x_1151_);
lean_dec_ref(v_post_1147_);
lean_dec_ref(v_pre_1146_);
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1215_, lean_object* v_pre_1216_, lean_object* v_e_1217_, lean_object* v_post_1218_, uint8_t v_usedLetOnly_1219_, uint8_t v_skipConstInApp_1220_, uint8_t v_skipInstances_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Core_checkSystem(v___x_1215_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1228_, 1);
lean_inc_ref(v_pre_1216_);
lean_inc(v___y_1226_);
lean_inc_ref(v___y_1225_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc_ref(v_e_1217_);
v___x_1229_ = lean_apply_6(v_pre_1216_, v_e_1217_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, lean_box(0));
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1278_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1278_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1278_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___y_1235_; 
switch(lean_obj_tag(v_a_1230_))
{
case 0:
{
lean_object* v_e_1270_; lean_object* v___x_1272_; 
lean_dec_ref(v_post_1218_);
lean_dec_ref(v_e_1217_);
lean_dec_ref(v_pre_1216_);
v_e_1270_ = lean_ctor_get(v_a_1230_, 0);
lean_inc_ref(v_e_1270_);
lean_dec_ref_known(v_a_1230_, 1);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v_e_1270_);
v___x_1272_ = v___x_1232_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_e_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
case 1:
{
lean_object* v_e_1274_; lean_object* v___x_1275_; 
lean_del_object(v___x_1232_);
lean_dec_ref(v_e_1217_);
v_e_1274_ = lean_ctor_get(v_a_1230_, 0);
lean_inc_ref(v_e_1274_);
lean_dec_ref_known(v_a_1230_, 1);
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v_e_1274_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1275_;
}
default: 
{
lean_object* v_e_x3f_1276_; 
lean_del_object(v___x_1232_);
v_e_x3f_1276_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_e_x3f_1276_);
lean_dec_ref_known(v_a_1230_, 1);
if (lean_obj_tag(v_e_x3f_1276_) == 0)
{
v___y_1235_ = v_e_1217_;
goto v___jp_1234_;
}
else
{
lean_object* v_val_1277_; 
lean_dec_ref(v_e_1217_);
v_val_1277_ = lean_ctor_get(v_e_x3f_1276_, 0);
lean_inc(v_val_1277_);
lean_dec_ref_known(v_e_x3f_1276_, 1);
v___y_1235_ = v_val_1277_;
goto v___jp_1234_;
}
}
}
v___jp_1234_:
{
switch(lean_obj_tag(v___y_1235_))
{
case 7:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___x_1236_, v___y_1235_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1237_;
}
case 6:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___x_1238_, v___y_1235_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1239_;
}
case 8:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___x_1240_, v___y_1235_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1241_;
}
case 5:
{
lean_object* v_dummy_1242_; lean_object* v_nargs_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_dummy_1242_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1243_ = l_Lean_Expr_getAppNumArgs(v___y_1235_);
lean_inc(v_nargs_1243_);
v___x_1244_ = lean_mk_array(v_nargs_1243_, v_dummy_1242_);
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_sub(v_nargs_1243_, v___x_1245_);
lean_dec(v_nargs_1243_);
v___x_1247_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1221_, v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v___y_1235_, v___x_1244_, v___x_1246_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1247_;
}
case 10:
{
lean_object* v_data_1248_; lean_object* v_expr_1249_; lean_object* v___x_1250_; 
v_data_1248_ = lean_ctor_get(v___y_1235_, 0);
v_expr_1249_ = lean_ctor_get(v___y_1235_, 1);
lean_inc_ref(v_expr_1249_);
lean_inc_ref(v_post_1218_);
lean_inc_ref(v_pre_1216_);
v___x_1250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v_expr_1249_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; size_t v___x_1252_; size_t v___x_1253_; uint8_t v___x_1254_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = lean_ptr_addr(v_expr_1249_);
v___x_1253_ = lean_ptr_addr(v_a_1251_);
v___x_1254_ = lean_usize_dec_eq(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_inc(v_data_1248_);
lean_dec_ref_known(v___y_1235_, 2);
v___x_1255_ = l_Lean_Expr_mdata___override(v_data_1248_, v_a_1251_);
v___x_1256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___x_1255_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_a_1251_);
v___x_1257_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___y_1235_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1257_;
}
}
else
{
lean_dec_ref_known(v___y_1235_, 2);
lean_dec_ref(v_post_1218_);
lean_dec_ref(v_pre_1216_);
return v___x_1250_;
}
}
case 11:
{
lean_object* v_typeName_1258_; lean_object* v_idx_1259_; lean_object* v_struct_1260_; lean_object* v___x_1261_; 
v_typeName_1258_ = lean_ctor_get(v___y_1235_, 0);
v_idx_1259_ = lean_ctor_get(v___y_1235_, 1);
v_struct_1260_ = lean_ctor_get(v___y_1235_, 2);
lean_inc_ref(v_struct_1260_);
lean_inc_ref(v_post_1218_);
lean_inc_ref(v_pre_1216_);
v___x_1261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v_struct_1260_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; size_t v___x_1263_; size_t v___x_1264_; uint8_t v___x_1265_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_ptr_addr(v_struct_1260_);
v___x_1264_ = lean_ptr_addr(v_a_1262_);
v___x_1265_ = lean_usize_dec_eq(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_inc(v_idx_1259_);
lean_inc(v_typeName_1258_);
lean_dec_ref_known(v___y_1235_, 3);
v___x_1266_ = l_Lean_Expr_proj___override(v_typeName_1258_, v_idx_1259_, v_a_1262_);
v___x_1267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___x_1266_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
lean_dec(v_a_1262_);
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___y_1235_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1268_;
}
}
else
{
lean_dec_ref_known(v___y_1235_, 3);
lean_dec_ref(v_post_1218_);
lean_dec_ref(v_pre_1216_);
return v___x_1261_;
}
}
default: 
{
lean_object* v___x_1269_; 
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1216_, v_post_1218_, v_usedLetOnly_1219_, v_skipConstInApp_1220_, v_skipInstances_1221_, v___y_1235_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v_post_1218_);
lean_dec_ref(v_e_1217_);
lean_dec_ref(v_pre_1216_);
v_a_1279_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1229_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1229_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_post_1218_);
lean_dec_ref(v_e_1217_);
lean_dec_ref(v_pre_1216_);
v_a_1287_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1228_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1228_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1295_, lean_object* v_pre_1296_, lean_object* v_e_1297_, lean_object* v_post_1298_, lean_object* v_usedLetOnly_1299_, lean_object* v_skipConstInApp_1300_, lean_object* v_skipInstances_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v_usedLetOnly_boxed_1308_; uint8_t v_skipConstInApp_boxed_1309_; uint8_t v_skipInstances_boxed_1310_; lean_object* v_res_1311_; 
v_usedLetOnly_boxed_1308_ = lean_unbox(v_usedLetOnly_1299_);
v_skipConstInApp_boxed_1309_ = lean_unbox(v_skipConstInApp_1300_);
v_skipInstances_boxed_1310_ = lean_unbox(v_skipInstances_1301_);
v_res_1311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1295_, v_pre_1296_, v_e_1297_, v_post_1298_, v_usedLetOnly_boxed_1308_, v_skipConstInApp_boxed_1309_, v_skipInstances_boxed_1310_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1312_, lean_object* v_post_1313_, uint8_t v_usedLetOnly_1314_, uint8_t v_skipConstInApp_1315_, uint8_t v_skipInstances_1316_, lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_inc(v_a_1318_);
v___x_1324_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1324_, 0, lean_box(0));
lean_closure_set(v___x_1324_, 1, lean_box(0));
lean_closure_set(v___x_1324_, 2, v_a_1318_);
v___x_1325_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1324_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1360_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1360_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1360_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1326_, v_e_1317_);
lean_dec(v_a_1326_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
lean_del_object(v___x_1328_);
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1332_ = lean_box(v_usedLetOnly_1314_);
v___x_1333_ = lean_box(v_skipConstInApp_1315_);
v___x_1334_ = lean_box(v_skipInstances_1316_);
lean_inc_ref(v_e_1317_);
v___f_1335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1335_, 0, v___x_1331_);
lean_closure_set(v___f_1335_, 1, v_pre_1312_);
lean_closure_set(v___f_1335_, 2, v_e_1317_);
lean_closure_set(v___f_1335_, 3, v_post_1313_);
lean_closure_set(v___f_1335_, 4, v___x_1332_);
lean_closure_set(v___f_1335_, 5, v___x_1333_);
lean_closure_set(v___f_1335_, 6, v___x_1334_);
v___x_1336_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1335_, v_a_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___f_1338_; lean_object* v___x_1339_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_n(v_a_1337_, 2);
lean_dec_ref_known(v___x_1336_, 1);
lean_inc(v_a_1318_);
v___f_1338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1338_, 0, v_a_1318_);
lean_closure_set(v___f_1338_, 1, v_e_1317_);
lean_closure_set(v___f_1338_, 2, v_a_1337_);
v___x_1339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1338_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1339_, 0);
lean_dec(v_unused_1347_);
v___x_1341_ = v___x_1339_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v___x_1339_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_a_1337_);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1337_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v_a_1337_);
v_a_1348_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1339_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1339_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_dec_ref(v_e_1317_);
return v___x_1336_;
}
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1358_; 
lean_dec_ref(v_e_1317_);
lean_dec_ref(v_post_1313_);
lean_dec_ref(v_pre_1312_);
v_val_1356_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1330_, 1);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_val_1356_);
v___x_1358_ = v___x_1328_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_val_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_e_1317_);
lean_dec_ref(v_post_1313_);
lean_dec_ref(v_pre_1312_);
v_a_1361_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1325_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1325_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1369_, lean_object* v_post_1370_, uint8_t v_usedLetOnly_1371_, uint8_t v_skipConstInApp_1372_, uint8_t v_skipInstances_1373_, lean_object* v_fvars_1374_, lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
if (lean_obj_tag(v_e_1375_) == 7)
{
lean_object* v_binderName_1382_; lean_object* v_binderType_1383_; lean_object* v_body_1384_; uint8_t v_binderInfo_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_binderName_1382_ = lean_ctor_get(v_e_1375_, 0);
lean_inc(v_binderName_1382_);
v_binderType_1383_ = lean_ctor_get(v_e_1375_, 1);
lean_inc_ref(v_binderType_1383_);
v_body_1384_ = lean_ctor_get(v_e_1375_, 2);
lean_inc_ref(v_body_1384_);
v_binderInfo_1385_ = lean_ctor_get_uint8(v_e_1375_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1375_, 3);
v___x_1386_ = lean_box(v_usedLetOnly_1371_);
v___x_1387_ = lean_box(v_skipConstInApp_1372_);
v___x_1388_ = lean_box(v_skipInstances_1373_);
lean_inc_ref(v_post_1370_);
lean_inc_ref(v_pre_1369_);
lean_inc_ref(v_fvars_1374_);
v___f_1389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1389_, 0, v_fvars_1374_);
lean_closure_set(v___f_1389_, 1, v_pre_1369_);
lean_closure_set(v___f_1389_, 2, v_post_1370_);
lean_closure_set(v___f_1389_, 3, v___x_1386_);
lean_closure_set(v___f_1389_, 4, v___x_1387_);
lean_closure_set(v___f_1389_, 5, v___x_1388_);
lean_closure_set(v___f_1389_, 6, v_body_1384_);
v___x_1390_ = lean_expr_instantiate_rev(v_binderType_1383_, v_fvars_1374_);
lean_dec_ref(v_fvars_1374_);
lean_dec_ref(v_binderType_1383_);
v___x_1391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v___x_1390_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = 0;
v___x_1394_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1382_, v_binderInfo_1385_, v_a_1392_, v___f_1389_, v___x_1393_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1394_;
}
else
{
lean_dec_ref(v___f_1389_);
lean_dec(v_binderName_1382_);
return v___x_1391_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_expr_instantiate_rev(v_e_1375_, v_fvars_1374_);
lean_dec_ref(v_e_1375_);
lean_inc_ref(v_post_1370_);
lean_inc_ref(v_pre_1369_);
v___x_1396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v___x_1395_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; uint8_t v___x_1398_; uint8_t v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = 0;
v___x_1399_ = 1;
v___x_1400_ = 1;
v___x_1401_ = l_Lean_Meta_mkForallFVars(v_fvars_1374_, v_a_1397_, v___x_1398_, v_usedLetOnly_1371_, v___x_1399_, v___x_1400_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec_ref(v_fvars_1374_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v_a_1402_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1403_;
}
else
{
lean_dec_ref(v_post_1370_);
lean_dec_ref(v_pre_1369_);
return v___x_1401_;
}
}
else
{
lean_dec_ref(v_fvars_1374_);
lean_dec_ref(v_post_1370_);
lean_dec_ref(v_pre_1369_);
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1404_, lean_object* v_pre_1405_, lean_object* v_post_1406_, uint8_t v_usedLetOnly_1407_, uint8_t v_skipConstInApp_1408_, uint8_t v_skipInstances_1409_, lean_object* v_body_1410_, lean_object* v_x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_array_push(v_fvars_1404_, v_x_1411_);
v___x_1419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1405_, v_post_1406_, v_usedLetOnly_1407_, v_skipConstInApp_1408_, v_skipInstances_1409_, v___x_1418_, v_body_1410_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1420_, lean_object* v_post_1421_, lean_object* v_usedLetOnly_1422_, lean_object* v_skipConstInApp_1423_, lean_object* v_skipInstances_1424_, lean_object* v_e_1425_, lean_object* v_a_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_usedLetOnly_boxed_1432_; uint8_t v_skipConstInApp_boxed_1433_; uint8_t v_skipInstances_boxed_1434_; lean_object* v_res_1435_; 
v_usedLetOnly_boxed_1432_ = lean_unbox(v_usedLetOnly_1422_);
v_skipConstInApp_boxed_1433_ = lean_unbox(v_skipConstInApp_1423_);
v_skipInstances_boxed_1434_ = lean_unbox(v_skipInstances_1424_);
v_res_1435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1420_, v_post_1421_, v_usedLetOnly_boxed_1432_, v_skipConstInApp_boxed_1433_, v_skipInstances_boxed_1434_, v_e_1425_, v_a_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v_a_1426_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1436_, lean_object* v_post_1437_, lean_object* v_usedLetOnly_1438_, lean_object* v_skipConstInApp_1439_, lean_object* v_skipInstances_1440_, lean_object* v_sz_1441_, lean_object* v_i_1442_, lean_object* v_bs_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_usedLetOnly_boxed_1450_; uint8_t v_skipConstInApp_boxed_1451_; uint8_t v_skipInstances_boxed_1452_; size_t v_sz_boxed_1453_; size_t v_i_boxed_1454_; lean_object* v_res_1455_; 
v_usedLetOnly_boxed_1450_ = lean_unbox(v_usedLetOnly_1438_);
v_skipConstInApp_boxed_1451_ = lean_unbox(v_skipConstInApp_1439_);
v_skipInstances_boxed_1452_ = lean_unbox(v_skipInstances_1440_);
v_sz_boxed_1453_ = lean_unbox_usize(v_sz_1441_);
lean_dec(v_sz_1441_);
v_i_boxed_1454_ = lean_unbox_usize(v_i_1442_);
lean_dec(v_i_1442_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1436_, v_post_1437_, v_usedLetOnly_boxed_1450_, v_skipConstInApp_boxed_1451_, v_skipInstances_boxed_1452_, v_sz_boxed_1453_, v_i_boxed_1454_, v_bs_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1456_, lean_object* v_post_1457_, lean_object* v_usedLetOnly_1458_, lean_object* v_skipConstInApp_1459_, lean_object* v_skipInstances_1460_, lean_object* v_e_1461_, lean_object* v_a_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_usedLetOnly_boxed_1468_; uint8_t v_skipConstInApp_boxed_1469_; uint8_t v_skipInstances_boxed_1470_; lean_object* v_res_1471_; 
v_usedLetOnly_boxed_1468_ = lean_unbox(v_usedLetOnly_1458_);
v_skipConstInApp_boxed_1469_ = lean_unbox(v_skipConstInApp_1459_);
v_skipInstances_boxed_1470_ = lean_unbox(v_skipInstances_1460_);
v_res_1471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1456_, v_post_1457_, v_usedLetOnly_boxed_1468_, v_skipConstInApp_boxed_1469_, v_skipInstances_boxed_1470_, v_e_1461_, v_a_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v_a_1462_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1472_, lean_object* v_post_1473_, lean_object* v_usedLetOnly_1474_, lean_object* v_skipConstInApp_1475_, lean_object* v_skipInstances_1476_, lean_object* v_fvars_1477_, lean_object* v_e_1478_, lean_object* v_a_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v_usedLetOnly_boxed_1485_; uint8_t v_skipConstInApp_boxed_1486_; uint8_t v_skipInstances_boxed_1487_; lean_object* v_res_1488_; 
v_usedLetOnly_boxed_1485_ = lean_unbox(v_usedLetOnly_1474_);
v_skipConstInApp_boxed_1486_ = lean_unbox(v_skipConstInApp_1475_);
v_skipInstances_boxed_1487_ = lean_unbox(v_skipInstances_1476_);
v_res_1488_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1472_, v_post_1473_, v_usedLetOnly_boxed_1485_, v_skipConstInApp_boxed_1486_, v_skipInstances_boxed_1487_, v_fvars_1477_, v_e_1478_, v_a_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v_a_1479_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1489_, lean_object* v_post_1490_, lean_object* v_usedLetOnly_1491_, lean_object* v_skipConstInApp_1492_, lean_object* v_skipInstances_1493_, lean_object* v_fvars_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_usedLetOnly_boxed_1502_; uint8_t v_skipConstInApp_boxed_1503_; uint8_t v_skipInstances_boxed_1504_; lean_object* v_res_1505_; 
v_usedLetOnly_boxed_1502_ = lean_unbox(v_usedLetOnly_1491_);
v_skipConstInApp_boxed_1503_ = lean_unbox(v_skipConstInApp_1492_);
v_skipInstances_boxed_1504_ = lean_unbox(v_skipInstances_1493_);
v_res_1505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1489_, v_post_1490_, v_usedLetOnly_boxed_1502_, v_skipConstInApp_boxed_1503_, v_skipInstances_boxed_1504_, v_fvars_1494_, v_e_1495_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_a_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1506_, lean_object* v_post_1507_, lean_object* v_usedLetOnly_1508_, lean_object* v_skipConstInApp_1509_, lean_object* v_skipInstances_1510_, lean_object* v_fvars_1511_, lean_object* v_e_1512_, lean_object* v_a_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_usedLetOnly_boxed_1519_; uint8_t v_skipConstInApp_boxed_1520_; uint8_t v_skipInstances_boxed_1521_; lean_object* v_res_1522_; 
v_usedLetOnly_boxed_1519_ = lean_unbox(v_usedLetOnly_1508_);
v_skipConstInApp_boxed_1520_ = lean_unbox(v_skipConstInApp_1509_);
v_skipInstances_boxed_1521_ = lean_unbox(v_skipInstances_1510_);
v_res_1522_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1506_, v_post_1507_, v_usedLetOnly_boxed_1519_, v_skipConstInApp_boxed_1520_, v_skipInstances_boxed_1521_, v_fvars_1511_, v_e_1512_, v_a_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v_a_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1523_, lean_object* v___x_1524_, lean_object* v_pre_1525_, lean_object* v_post_1526_, lean_object* v_usedLetOnly_1527_, lean_object* v_skipConstInApp_1528_, lean_object* v_skipInstances_1529_, lean_object* v_a_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v_usedLetOnly_boxed_1538_; uint8_t v_skipConstInApp_boxed_1539_; uint8_t v_skipInstances_boxed_1540_; lean_object* v_res_1541_; 
v_usedLetOnly_boxed_1538_ = lean_unbox(v_usedLetOnly_1527_);
v_skipConstInApp_boxed_1539_ = lean_unbox(v_skipConstInApp_1528_);
v_skipInstances_boxed_1540_ = lean_unbox(v_skipInstances_1529_);
v_res_1541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1523_, v___x_1524_, v_pre_1525_, v_post_1526_, v_usedLetOnly_boxed_1538_, v_skipConstInApp_boxed_1539_, v_skipInstances_boxed_1540_, v_a_1530_, v_b_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___x_1524_);
lean_dec(v_upperBound_1523_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1542_, lean_object* v_pre_1543_, lean_object* v_post_1544_, lean_object* v_usedLetOnly_1545_, lean_object* v_skipConstInApp_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v_skipInstances_boxed_1556_; uint8_t v_usedLetOnly_boxed_1557_; uint8_t v_skipConstInApp_boxed_1558_; lean_object* v_res_1559_; 
v_skipInstances_boxed_1556_ = lean_unbox(v_skipInstances_1542_);
v_usedLetOnly_boxed_1557_ = lean_unbox(v_usedLetOnly_1545_);
v_skipConstInApp_boxed_1558_ = lean_unbox(v_skipConstInApp_1546_);
v_res_1559_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1556_, v_pre_1543_, v_post_1544_, v_usedLetOnly_boxed_1557_, v_skipConstInApp_boxed_1558_, v_x_1547_, v_x_1548_, v_x_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
return v_res_1559_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_unsigned_to_nat(16u);
v___x_1562_ = lean_mk_array(v___x_1561_, v___x_1560_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1563_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1567_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1567_, 0, lean_box(0));
lean_closure_set(v___x_1567_, 1, lean_box(0));
lean_closure_set(v___x_1567_, 2, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1568_, lean_object* v_pre_1569_, lean_object* v_post_1570_, uint8_t v_usedLetOnly_1571_, uint8_t v_skipConstInApp_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_a_1581_; lean_object* v___x_1582_; 
v___x_1578_ = 0;
v___x_1579_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1580_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1579_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1569_, v_post_1570_, v_usedLetOnly_1571_, v_skipConstInApp_1572_, v___x_1578_, v_input_1568_, v_a_1581_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1584_, 0, lean_box(0));
lean_closure_set(v___x_1584_, 1, lean_box(0));
lean_closure_set(v___x_1584_, 2, v_a_1581_);
v___x_1585_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1584_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1585_, 0);
lean_dec(v_unused_1593_);
v___x_1587_ = v___x_1585_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_dec(v___x_1585_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_a_1583_);
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1583_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_dec(v_a_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1594_, lean_object* v_pre_1595_, lean_object* v_post_1596_, lean_object* v_usedLetOnly_1597_, lean_object* v_skipConstInApp_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v_usedLetOnly_boxed_1604_; uint8_t v_skipConstInApp_boxed_1605_; lean_object* v_res_1606_; 
v_usedLetOnly_boxed_1604_ = lean_unbox(v_usedLetOnly_1597_);
v_skipConstInApp_boxed_1605_ = lean_unbox(v_skipConstInApp_1598_);
v_res_1606_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1594_, v_pre_1595_, v_post_1596_, v_usedLetOnly_boxed_1604_, v_skipConstInApp_boxed_1605_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___f_1615_; lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1628_; 
v___f_1615_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1616_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1609_, v_a_1613_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_unbox(v_a_1617_);
lean_dec(v_a_1617_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1623_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_e_1609_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_e_1609_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_del_object(v___x_1619_);
v___x_1625_ = 0;
v___x_1626_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1627_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1609_, v___x_1626_, v___f_1615_, v___x_1625_, v___x_1625_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1636_, lean_object* v___x_1637_, lean_object* v_pre_1638_, lean_object* v_post_1639_, uint8_t v_usedLetOnly_1640_, uint8_t v_skipConstInApp_1641_, uint8_t v_skipInstances_1642_, lean_object* v___x_1643_, lean_object* v_inst_1644_, lean_object* v_R_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_c_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1636_, v___x_1637_, v_pre_1638_, v_post_1639_, v_usedLetOnly_1640_, v_skipConstInApp_1641_, v_skipInstances_1642_, v_a_1646_, v_b_1647_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1656_ = _args[0];
lean_object* v___x_1657_ = _args[1];
lean_object* v_pre_1658_ = _args[2];
lean_object* v_post_1659_ = _args[3];
lean_object* v_usedLetOnly_1660_ = _args[4];
lean_object* v_skipConstInApp_1661_ = _args[5];
lean_object* v_skipInstances_1662_ = _args[6];
lean_object* v___x_1663_ = _args[7];
lean_object* v_inst_1664_ = _args[8];
lean_object* v_R_1665_ = _args[9];
lean_object* v_a_1666_ = _args[10];
lean_object* v_b_1667_ = _args[11];
lean_object* v_c_1668_ = _args[12];
lean_object* v___y_1669_ = _args[13];
lean_object* v___y_1670_ = _args[14];
lean_object* v___y_1671_ = _args[15];
lean_object* v___y_1672_ = _args[16];
lean_object* v___y_1673_ = _args[17];
lean_object* v___y_1674_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1675_; uint8_t v_skipConstInApp_boxed_1676_; uint8_t v_skipInstances_boxed_1677_; lean_object* v_res_1678_; 
v_usedLetOnly_boxed_1675_ = lean_unbox(v_usedLetOnly_1660_);
v_skipConstInApp_boxed_1676_ = lean_unbox(v_skipConstInApp_1661_);
v_skipInstances_boxed_1677_ = lean_unbox(v_skipInstances_1662_);
v_res_1678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1656_, v___x_1657_, v_pre_1658_, v_post_1659_, v_usedLetOnly_boxed_1675_, v_skipConstInApp_boxed_1676_, v_skipInstances_boxed_1677_, v___x_1663_, v_inst_1664_, v_R_1665_, v_a_1666_, v_b_1667_, v_c_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec(v___x_1663_);
lean_dec_ref(v___x_1657_);
lean_dec(v_upperBound_1656_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1679_, lean_object* v_m_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1680_, v_a_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1683_, lean_object* v_m_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1683_, v_m_1684_, v_a_1685_);
lean_dec_ref(v_a_1685_);
lean_dec_ref(v_m_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1687_, lean_object* v_name_1688_, uint8_t v_bi_1689_, lean_object* v_type_1690_, lean_object* v_k_1691_, uint8_t v_kind_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1688_, v_bi_1689_, v_type_1690_, v_k_1691_, v_kind_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_name_1701_, lean_object* v_bi_1702_, lean_object* v_type_1703_, lean_object* v_k_1704_, lean_object* v_kind_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v_bi_boxed_1712_; uint8_t v_kind_boxed_1713_; lean_object* v_res_1714_; 
v_bi_boxed_1712_ = lean_unbox(v_bi_1702_);
v_kind_boxed_1713_ = lean_unbox(v_kind_1705_);
v_res_1714_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1700_, v_name_1701_, v_bi_boxed_1712_, v_type_1703_, v_k_1704_, v_kind_boxed_1713_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1715_, lean_object* v_name_1716_, lean_object* v_type_1717_, lean_object* v_val_1718_, lean_object* v_k_1719_, uint8_t v_nondep_1720_, uint8_t v_kind_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1716_, v_type_1717_, v_val_1718_, v_k_1719_, v_nondep_1720_, v_kind_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_name_1730_, lean_object* v_type_1731_, lean_object* v_val_1732_, lean_object* v_k_1733_, lean_object* v_nondep_1734_, lean_object* v_kind_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_nondep_boxed_1742_; uint8_t v_kind_boxed_1743_; lean_object* v_res_1744_; 
v_nondep_boxed_1742_ = lean_unbox(v_nondep_1734_);
v_kind_boxed_1743_ = lean_unbox(v_kind_1735_);
v_res_1744_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1729_, v_name_1730_, v_type_1731_, v_val_1732_, v_k_1733_, v_nondep_boxed_1742_, v_kind_boxed_1743_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1745_, lean_object* v_ref_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1746_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1753_, lean_object* v_ref_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1753_, v_ref_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_x_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1770_, v_x_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1779_, lean_object* v_m_1780_, lean_object* v_a_1781_, lean_object* v_b_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1780_, v_a_1781_, v_b_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1784_, lean_object* v_a_1785_, lean_object* v_x_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1785_, v_x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1788_, lean_object* v_a_1789_, lean_object* v_x_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1788_, v_a_1789_, v_x_1790_);
lean_dec(v_x_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1792_, lean_object* v_a_1793_, lean_object* v_x_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1793_, v_x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1796_, lean_object* v_a_1797_, lean_object* v_x_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1796_, v_a_1797_, v_x_1798_);
lean_dec(v_x_1798_);
lean_dec_ref(v_a_1797_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1801_, lean_object* v_data_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1804_, lean_object* v_a_1805_, lean_object* v_b_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1805_, v_b_1806_, v_x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1809_, lean_object* v_i_1810_, lean_object* v_source_1811_, lean_object* v_target_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1810_, v_source_1811_, v_target_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_x_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_x_1826_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v_env_1840_; uint8_t v___x_1841_; lean_object* v_env_1842_; lean_object* v___x_1843_; lean_object* v_toCold_1844_; lean_object* v_mctx_1845_; lean_object* v_lctx_1846_; lean_object* v_options_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1839_ = lean_st_ref_get(v___y_1837_);
v_env_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_env_1840_);
lean_dec(v___x_1839_);
v___x_1841_ = 0;
v_env_1842_ = l_Lean_Environment_setRecordingDeps(v_env_1840_, v___x_1841_);
v___x_1843_ = lean_st_ref_get(v___y_1835_);
v_toCold_1844_ = lean_ctor_get(v___y_1836_, 0);
v_mctx_1845_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_mctx_1845_);
lean_dec(v___x_1843_);
v_lctx_1846_ = lean_ctor_get(v___y_1834_, 2);
v_options_1847_ = lean_ctor_get(v_toCold_1844_, 2);
lean_inc_ref(v_options_1847_);
lean_inc_ref(v_lctx_1846_);
v___x_1848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1848_, 0, v_env_1842_);
lean_ctor_set(v___x_1848_, 1, v_mctx_1845_);
lean_ctor_set(v___x_1848_, 2, v_lctx_1846_);
lean_ctor_set(v___x_1848_, 3, v_options_1847_);
v___x_1849_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_msgData_1833_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1858_; double v___x_1859_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_float_of_nat(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_ref_1870_; lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1917_; 
v_ref_1870_ = lean_ctor_get(v___y_1867_, 2);
v___x_1871_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1917_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1917_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v_traceState_1877_; lean_object* v_env_1878_; lean_object* v_nextMacroScope_1879_; lean_object* v_ngen_1880_; lean_object* v_auxDeclNGen_1881_; lean_object* v_cache_1882_; lean_object* v_recordedDeps_1883_; lean_object* v_messages_1884_; lean_object* v_infoState_1885_; lean_object* v_snapshotTasks_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1916_; 
v___x_1876_ = lean_st_ref_take(v___y_1868_);
v_traceState_1877_ = lean_ctor_get(v___x_1876_, 4);
v_env_1878_ = lean_ctor_get(v___x_1876_, 0);
v_nextMacroScope_1879_ = lean_ctor_get(v___x_1876_, 1);
v_ngen_1880_ = lean_ctor_get(v___x_1876_, 2);
v_auxDeclNGen_1881_ = lean_ctor_get(v___x_1876_, 3);
v_cache_1882_ = lean_ctor_get(v___x_1876_, 5);
v_recordedDeps_1883_ = lean_ctor_get(v___x_1876_, 6);
v_messages_1884_ = lean_ctor_get(v___x_1876_, 7);
v_infoState_1885_ = lean_ctor_get(v___x_1876_, 8);
v_snapshotTasks_1886_ = lean_ctor_get(v___x_1876_, 9);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1888_ = v___x_1876_;
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snapshotTasks_1886_);
lean_inc(v_infoState_1885_);
lean_inc(v_messages_1884_);
lean_inc(v_recordedDeps_1883_);
lean_inc(v_cache_1882_);
lean_inc(v_traceState_1877_);
lean_inc(v_auxDeclNGen_1881_);
lean_inc(v_ngen_1880_);
lean_inc(v_nextMacroScope_1879_);
lean_inc(v_env_1878_);
lean_dec(v___x_1876_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
uint64_t v_tid_1890_; lean_object* v_traces_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1915_; 
v_tid_1890_ = lean_ctor_get_uint64(v_traceState_1877_, sizeof(void*)*1);
v_traces_1891_ = lean_ctor_get(v_traceState_1877_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_traceState_1877_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1893_ = v_traceState_1877_;
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_traces_1891_);
lean_dec(v_traceState_1877_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; double v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1898_ = 0;
v___x_1899_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1900_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1900_, 0, v_cls_1863_);
lean_ctor_set(v___x_1900_, 1, v___x_1896_);
lean_ctor_set(v___x_1900_, 2, v___x_1899_);
lean_ctor_set_float(v___x_1900_, sizeof(void*)*3, v___x_1897_);
lean_ctor_set_float(v___x_1900_, sizeof(void*)*3 + 8, v___x_1897_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*3 + 16, v___x_1898_);
v___x_1901_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1902_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v_a_1872_);
lean_ctor_set(v___x_1902_, 2, v___x_1901_);
lean_inc(v_ref_1870_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v_ref_1870_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_PersistentArray_push___redArg(v_traces_1891_, v___x_1903_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1904_);
v___x_1906_ = v___x_1893_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1904_);
lean_ctor_set_uint64(v_reuseFailAlloc_1914_, sizeof(void*)*1, v_tid_1890_);
v___x_1906_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 4, v___x_1906_);
v___x_1908_ = v___x_1888_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_env_1878_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_nextMacroScope_1879_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_ngen_1880_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_auxDeclNGen_1881_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_cache_1882_);
lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_recordedDeps_1883_);
lean_ctor_set(v_reuseFailAlloc_1913_, 7, v_messages_1884_);
lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_infoState_1885_);
lean_ctor_set(v_reuseFailAlloc_1913_, 9, v_snapshotTasks_1886_);
v___x_1908_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_st_ref_put(v___y_1868_, v___x_1908_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1895_);
v___x_1911_ = v___x_1874_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1895_);
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
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__1));
v___x_1931_ = l_Lean_Name_append(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__3));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__5));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__7));
v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__9));
v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_e_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___y_1951_; 
if (lean_obj_tag(v_e_1944_) == 11)
{
lean_object* v_typeName_1975_; lean_object* v_idx_1976_; lean_object* v_struct_1977_; lean_object* v___x_1978_; lean_object* v_env_1979_; lean_object* v___x_1980_; 
v_typeName_1975_ = lean_ctor_get(v_e_1944_, 0);
v_idx_1976_ = lean_ctor_get(v_e_1944_, 1);
v_struct_1977_ = lean_ctor_get(v_e_1944_, 2);
v___x_1978_ = lean_st_ref_get(v___y_1948_);
v_env_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc_ref(v_env_1979_);
lean_dec(v___x_1978_);
lean_inc(v_typeName_1975_);
v___x_1980_ = l_Lean_getStructureInfo_x3f(v_env_1979_, v_typeName_1975_);
if (lean_obj_tag(v___x_1980_) == 1)
{
lean_object* v_val_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2035_; 
v_val_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2035_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_val_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2035_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_fieldNames_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_fieldNames_1985_ = lean_ctor_get(v_val_1981_, 1);
lean_inc_ref(v_fieldNames_1985_);
lean_dec(v_val_1981_);
v___x_1986_ = lean_array_get_size(v_fieldNames_1985_);
v___x_1987_ = lean_nat_dec_lt(v_idx_1976_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v_toCold_1988_; lean_object* v_options_1989_; uint8_t v_hasTrace_1990_; 
lean_dec_ref(v_fieldNames_1985_);
v_toCold_1988_ = lean_ctor_get(v___y_1947_, 0);
v_options_1989_ = lean_ctor_get(v_toCold_1988_, 2);
v_hasTrace_1990_ = lean_ctor_get_uint8(v_options_1989_, sizeof(void*)*1);
if (v_hasTrace_1990_ == 0)
{
lean_del_object(v___x_1983_);
goto v___jp_1972_;
}
else
{
lean_object* v_inheritedTraceOptions_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_inheritedTraceOptions_1991_ = lean_ctor_get(v_toCold_1988_, 11);
v___x_1992_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1993_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1991_, v_options_1989_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_del_object(v___x_1983_);
goto v___jp_1972_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1995_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4);
lean_inc(v_idx_1976_);
v___x_1996_ = l_Nat_reprFast(v_idx_1976_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 3);
lean_ctor_set(v___x_1983_, 0, v___x_1996_);
v___x_1998_ = v___x_1983_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_2014_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_1999_ = l_Lean_MessageData_ofFormat(v___x_1998_);
v___x_2000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1995_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
lean_inc_ref(v_e_1944_);
v___x_2003_ = l_Lean_indentExpr(v_e_1944_);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1992_, v___x_2004_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_dec_ref_known(v___x_2005_, 1);
goto v___jp_1972_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref_known(v_e_1944_, 3);
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2015_; uint8_t v_transparency_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; uint8_t v___x_2019_; 
lean_inc_ref(v_struct_1977_);
lean_inc(v_idx_1976_);
lean_del_object(v___x_1983_);
lean_dec_ref_known(v_e_1944_, 3);
v___x_2015_ = l_Lean_Meta_Context_config(v___y_1945_);
v_transparency_2016_ = lean_ctor_get_uint8(v___x_2015_, 9);
lean_dec_ref(v___x_2015_);
v___x_2017_ = lean_array_fget(v_fieldNames_1985_, v_idx_1976_);
lean_dec(v_idx_1976_);
lean_dec_ref(v_fieldNames_1985_);
v___x_2018_ = 1;
v___x_2019_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2016_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v_keyedConfig_2020_; uint8_t v_trackZetaDelta_2021_; lean_object* v_zetaDeltaSet_2022_; lean_object* v_lctx_2023_; lean_object* v_localInstances_2024_; lean_object* v_defEqCtx_x3f_2025_; lean_object* v_synthPendingDepth_2026_; lean_object* v_customCanUnfoldPredicate_x3f_2027_; uint8_t v_univApprox_2028_; uint8_t v_inTypeClassResolution_2029_; uint8_t v_cacheInferType_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_keyedConfig_2020_ = lean_ctor_get(v___y_1945_, 0);
v_trackZetaDelta_2021_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7);
v_zetaDeltaSet_2022_ = lean_ctor_get(v___y_1945_, 1);
v_lctx_2023_ = lean_ctor_get(v___y_1945_, 2);
v_localInstances_2024_ = lean_ctor_get(v___y_1945_, 3);
v_defEqCtx_x3f_2025_ = lean_ctor_get(v___y_1945_, 4);
v_synthPendingDepth_2026_ = lean_ctor_get(v___y_1945_, 5);
v_customCanUnfoldPredicate_x3f_2027_ = lean_ctor_get(v___y_1945_, 6);
v_univApprox_2028_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2029_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7 + 2);
v_cacheInferType_2030_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2020_);
v___x_2031_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2018_, v_keyedConfig_2020_);
lean_inc(v_customCanUnfoldPredicate_x3f_2027_);
lean_inc(v_synthPendingDepth_2026_);
lean_inc(v_defEqCtx_x3f_2025_);
lean_inc_ref(v_localInstances_2024_);
lean_inc_ref(v_lctx_2023_);
lean_inc(v_zetaDeltaSet_2022_);
v___x_2032_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v_zetaDeltaSet_2022_);
lean_ctor_set(v___x_2032_, 2, v_lctx_2023_);
lean_ctor_set(v___x_2032_, 3, v_localInstances_2024_);
lean_ctor_set(v___x_2032_, 4, v_defEqCtx_x3f_2025_);
lean_ctor_set(v___x_2032_, 5, v_synthPendingDepth_2026_);
lean_ctor_set(v___x_2032_, 6, v_customCanUnfoldPredicate_x3f_2027_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7, v_trackZetaDelta_2021_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7 + 1, v_univApprox_2028_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2029_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*7 + 3, v_cacheInferType_2030_);
v___x_2033_ = l_Lean_Meta_mkProjection(v_struct_1977_, v___x_2017_, v___x_2032_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec_ref_known(v___x_2032_, 7);
v___y_1951_ = v___x_2033_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Meta_mkProjection(v_struct_1977_, v___x_2017_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
v___y_1951_ = v___x_2034_;
goto v___jp_1950_;
}
}
}
}
else
{
lean_object* v_toCold_2036_; lean_object* v_options_2037_; uint8_t v_hasTrace_2038_; 
lean_dec(v___x_1980_);
v_toCold_2036_ = lean_ctor_get(v___y_1947_, 0);
v_options_2037_ = lean_ctor_get(v_toCold_2036_, 2);
v_hasTrace_2038_ = lean_ctor_get_uint8(v_options_2037_, sizeof(void*)*1);
if (v_hasTrace_2038_ == 0)
{
goto v___jp_1969_;
}
else
{
lean_object* v_inheritedTraceOptions_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_inheritedTraceOptions_2039_ = lean_ctor_get(v_toCold_2036_, 11);
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2041_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2042_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2039_, v_options_2037_, v___x_2041_);
if (v___x_2042_ == 0)
{
goto v___jp_1969_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2043_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8);
lean_inc(v_typeName_1975_);
v___x_2044_ = l_Lean_MessageData_ofName(v_typeName_1975_);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10);
v___x_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
lean_inc_ref(v_e_1944_);
v___x_2048_ = l_Lean_indentExpr(v_e_1944_);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2040_, v___x_2049_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_dec_ref_known(v___x_2050_, 1);
goto v___jp_1969_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref_known(v_e_1944_, 3);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_e_1944_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
v___jp_1950_:
{
if (lean_obj_tag(v___y_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_a_1952_ = lean_ctor_get(v___y_1951_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___y_1951_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v___y_1951_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___y_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1961_ = lean_ctor_get(v___y_1951_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___y_1951_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___y_1951_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___y_1951_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
v___jp_1969_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_e_1944_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
v___jp_1972_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_e_1944_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_e_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___f_2077_; lean_object* v___x_2078_; 
v___f_2077_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2078_ = lean_find_expr(v___f_2077_, v_e_2071_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_e_2071_);
return v___x_2079_;
}
else
{
lean_object* v___f_2080_; lean_object* v_post_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref_known(v___x_2078_, 1);
v___f_2080_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v_post_2081_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2082_ = 0;
v___x_2083_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2071_, v___f_2080_, v_post_2081_, v___x_2082_, v___x_2082_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Meta_Sym_foldProjs(v_e_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
return v_res_2090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2096_ = l_Lean_mkConst(v___x_2095_, v___x_2094_);
return v___x_2096_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_box(0);
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2102_ = l_Lean_mkConst(v___x_2101_, v___x_2100_);
return v___x_2102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_box(0);
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2110_ = l_Lean_mkConst(v___x_2109_, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_box(0);
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2117_ = l_Lean_mkConst(v___x_2116_, v___x_2115_);
return v___x_2117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l_Lean_mkNatLit(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_box(0);
v___x_2126_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2127_ = l_Lean_mkConst(v___x_2126_, v___x_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2131_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2130_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
v_a_2133_ = lean_ctor_get(v___x_2131_, 1);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2131_, 2);
v___x_2134_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2135_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2134_, v_a_2128_, v_a_2133_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
v_a_2137_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2135_, 2);
v___x_2138_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2139_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2138_, v_a_2128_, v_a_2137_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
v_a_2141_ = lean_ctor_get(v___x_2139_, 1);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2139_, 2);
v___x_2142_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2143_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2142_, v_a_2128_, v_a_2141_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
v_a_2145_ = lean_ctor_get(v___x_2143_, 1);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2143_, 2);
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2147_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2146_, v_a_2128_, v_a_2145_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
v_a_2149_ = lean_ctor_get(v___x_2147_, 1);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2147_, 2);
v___x_2150_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2151_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2150_, v_a_2128_, v_a_2149_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
v_a_2153_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2151_, 2);
v___x_2154_ = l_Lean_Int_mkType;
v___x_2155_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2154_, v_a_2128_, v_a_2153_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2165_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_a_2157_ = lean_ctor_get(v___x_2155_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2159_ = v___x_2155_;
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2136_);
lean_ctor_set(v___x_2161_, 1, v_a_2132_);
lean_ctor_set(v___x_2161_, 2, v_a_2148_);
lean_ctor_set(v___x_2161_, 3, v_a_2144_);
lean_ctor_set(v___x_2161_, 4, v_a_2140_);
lean_ctor_set(v___x_2161_, 5, v_a_2152_);
lean_ctor_set(v___x_2161_, 6, v_a_2156_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_a_2157_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2152_);
lean_dec(v_a_2148_);
lean_dec(v_a_2144_);
lean_dec(v_a_2140_);
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
v_a_2166_ = lean_ctor_get(v___x_2155_, 0);
v_a_2167_ = lean_ctor_get(v___x_2155_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2155_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_inc(v_a_2166_);
lean_dec(v___x_2155_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2166_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2148_);
lean_dec(v_a_2144_);
lean_dec(v_a_2140_);
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
v_a_2175_ = lean_ctor_get(v___x_2151_, 0);
v_a_2176_ = lean_ctor_get(v___x_2151_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2151_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_inc(v_a_2175_);
lean_dec(v___x_2151_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2144_);
lean_dec(v_a_2140_);
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
v_a_2184_ = lean_ctor_get(v___x_2147_, 0);
v_a_2185_ = lean_ctor_get(v___x_2147_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2147_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_inc(v_a_2184_);
lean_dec(v___x_2147_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2184_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_2140_);
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
v_a_2193_ = lean_ctor_get(v___x_2143_, 0);
v_a_2194_ = lean_ctor_get(v___x_2143_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2143_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_inc(v_a_2193_);
lean_dec(v___x_2143_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2193_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_a_2136_);
lean_dec(v_a_2132_);
v_a_2202_ = lean_ctor_get(v___x_2139_, 0);
v_a_2203_ = lean_ctor_get(v___x_2139_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2139_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_inc(v_a_2202_);
lean_dec(v___x_2139_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2202_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2132_);
v_a_2211_ = lean_ctor_get(v___x_2135_, 0);
v_a_2212_ = lean_ctor_get(v___x_2135_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2135_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_inc(v_a_2211_);
lean_dec(v___x_2135_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2211_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_a_2220_ = lean_ctor_get(v___x_2131_, 0);
v_a_2221_ = lean_ctor_get(v___x_2131_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2131_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_inc(v_a_2220_);
lean_dec(v___x_2131_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2220_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2229_, v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2232_, lean_object* v_opt_2233_){
_start:
{
lean_object* v_name_2234_; lean_object* v_defValue_2235_; lean_object* v_map_2236_; lean_object* v___x_2237_; 
v_name_2234_ = lean_ctor_get(v_opt_2233_, 0);
v_defValue_2235_ = lean_ctor_get(v_opt_2233_, 1);
v_map_2236_ = lean_ctor_get(v_opts_2232_, 0);
v___x_2237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2236_, v_name_2234_);
if (lean_obj_tag(v___x_2237_) == 0)
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_unbox(v_defValue_2235_);
return v___x_2238_;
}
else
{
lean_object* v_val_2239_; 
v_val_2239_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v___x_2237_, 1);
if (lean_obj_tag(v_val_2239_) == 1)
{
uint8_t v_v_2240_; 
v_v_2240_ = lean_ctor_get_uint8(v_val_2239_, 0);
lean_dec_ref_known(v_val_2239_, 0);
return v_v_2240_;
}
else
{
uint8_t v___x_2241_; 
lean_dec(v_val_2239_);
v___x_2241_ = lean_unbox(v_defValue_2235_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2242_, lean_object* v_opt_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2242_, v_opt_2243_);
lean_dec_ref(v_opt_2243_);
lean_dec_ref(v_opts_2242_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg(){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object* v___dummy_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v_res_2252_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___f_2263_; lean_object* v___x_2208__overap_2264_; lean_object* v___x_2265_; 
v___f_2263_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2208__overap_2264_ = lean_panic_fn_borrowed(v___f_2263_, v_msg_2257_);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
lean_inc(v___y_2259_);
lean_inc_ref(v___y_2258_);
v___x_2265_ = lean_apply_5(v___x_2208__overap_2264_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, lean_box(0));
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2272_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2280_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2281_ = lean_unsigned_to_nat(19u);
v___x_2282_ = lean_unsigned_to_nat(309u);
v___x_2283_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__3));
v___x_2284_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_2285_ = l_mkPanicMessageWithDecl(v___x_2284_, v___x_2283_, v___x_2282_, v___x_2281_, v___x_2280_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_fst_2293_; lean_object* v_snd_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___x_2334_; lean_object* v_env_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2334_ = lean_st_ref_get(v_a_2290_);
v_env_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc_ref(v_env_2335_);
lean_dec(v___x_2334_);
v___x_2336_ = 0;
v___x_2337_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2337_, 0, v_env_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2336_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1 + 1, v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2339_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2337_, v___x_2338_);
lean_dec_ref_known(v___x_2337_, 1);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v_a_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
v_a_2341_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2339_, 2);
v_fst_2293_ = v_a_2340_;
v_snd_2294_ = v_a_2341_;
v___y_2295_ = v_a_2287_;
v___y_2296_ = v_a_2288_;
v___y_2297_ = v_a_2289_;
v___y_2298_ = v_a_2290_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec_ref_known(v___x_2339_, 2);
v___x_2342_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__5, &l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5);
v___x_2343_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2342_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v_fst_2345_; lean_object* v_snd_2346_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_fst_2345_ = lean_ctor_get(v_a_2344_, 0);
lean_inc(v_fst_2345_);
v_snd_2346_ = lean_ctor_get(v_a_2344_, 1);
lean_inc(v_snd_2346_);
lean_dec(v_a_2344_);
v_fst_2293_ = v_fst_2345_;
v_snd_2294_ = v_snd_2346_;
v___y_2295_ = v_a_2287_;
v___y_2296_ = v_a_2288_;
v___y_2297_ = v_a_2289_;
v___y_2298_ = v_a_2290_;
goto v___jp_2292_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v_x_2286_);
v_a_2347_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2343_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2343_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
v___jp_2292_:
{
lean_object* v_ref_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v_ref_2299_ = lean_ctor_get(v___y_2297_, 2);
v___x_2300_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2297_);
v___x_2301_ = l_Lean_Meta_Sym_sym_debug;
v___x_2302_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v___x_2300_, v___x_2301_);
lean_dec_ref(v___x_2300_);
v___x_2303_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_fst_2293_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2310_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v___x_2310_, 0, v_snd_2294_);
lean_ctor_set(v___x_2310_, 1, v___x_2307_);
lean_ctor_set(v___x_2310_, 2, v___x_2307_);
lean_ctor_set(v___x_2310_, 3, v___x_2307_);
lean_ctor_set(v___x_2310_, 4, v___x_2307_);
lean_ctor_set(v___x_2310_, 5, v___x_2307_);
lean_ctor_set(v___x_2310_, 6, v___x_2307_);
lean_ctor_set(v___x_2310_, 7, v___x_2307_);
lean_ctor_set(v___x_2310_, 8, v___x_2307_);
lean_ctor_set(v___x_2310_, 9, v_a_2304_);
lean_ctor_set(v___x_2310_, 10, v___x_2308_);
lean_ctor_set(v___x_2310_, 11, v___x_2309_);
lean_ctor_set(v___x_2310_, 12, v___x_2307_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*13, v___x_2302_);
v___x_2311_ = lean_st_mk_ref(v___x_2310_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___x_2311_);
v___x_2312_ = lean_apply_7(v_x_2286_, v___x_2306_, v___x_2311_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, lean_box(0));
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2321_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_st_ref_get(v___x_2311_);
lean_dec(v___x_2311_);
lean_dec(v___x_2317_);
if (v_isShared_2316_ == 0)
{
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2313_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_dec(v___x_2311_);
return v___x_2312_;
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_snd_2294_);
lean_dec_ref(v_fst_2293_);
lean_dec_ref(v_x_2286_);
v_a_2322_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2324_ = v___x_2303_;
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2303_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2326_ = lean_io_error_to_string(v_a_2322_);
v___x_2327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = l_Lean_MessageData_ofFormat(v___x_2327_);
lean_inc(v_ref_2299_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_ref_2299_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2329_);
v___x_2331_ = v___x_2324_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2362_, lean_object* v_x_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_x_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2370_, v_x_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2378_){
_start:
{
lean_object* v_sharedExprs_2380_; lean_object* v___x_2381_; 
v_sharedExprs_2380_ = lean_ctor_get(v_a_2378_, 0);
lean_inc_ref(v_sharedExprs_2380_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_sharedExprs_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2382_);
lean_dec_ref(v_a_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2385_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2412_; 
v___x_2403_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2401_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_trueExpr_2408_; lean_object* v___x_2410_; 
v_trueExpr_2408_ = lean_ctor_get(v_a_2404_, 0);
lean_inc_ref(v_trueExpr_2408_);
lean_dec(v_a_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v_trueExpr_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_trueExpr_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2413_);
lean_dec_ref(v_a_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2416_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2433_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2447_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
size_t v___x_2440_; size_t v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2440_ = lean_ptr_addr(v_e_2432_);
v___x_2441_ = lean_ptr_addr(v_a_2436_);
lean_dec(v_a_2436_);
v___x_2442_ = lean_usize_dec_eq(v___x_2440_, v___x_2441_);
v___x_2443_ = lean_box(v___x_2442_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2443_);
v___x_2445_ = v___x_2438_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2435_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2435_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2456_, v_a_2457_);
lean_dec_ref(v_a_2457_);
lean_dec_ref(v_e_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2460_, v_a_2461_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_e_2469_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2478_){
_start:
{
lean_object* v___x_2480_; lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2489_; 
v___x_2480_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2478_);
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2489_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2489_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_falseExpr_2485_; lean_object* v___x_2487_; 
v_falseExpr_2485_ = lean_ctor_get(v_a_2481_, 1);
lean_inc_ref(v_falseExpr_2485_);
lean_dec(v_a_2481_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v_falseExpr_2485_);
v___x_2487_ = v___x_2483_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_falseExpr_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2490_);
lean_dec_ref(v_a_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2493_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2510_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2524_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2524_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2524_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
size_t v___x_2517_; size_t v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2517_ = lean_ptr_addr(v_e_2509_);
v___x_2518_ = lean_ptr_addr(v_a_2513_);
lean_dec(v_a_2513_);
v___x_2519_ = lean_usize_dec_eq(v___x_2517_, v___x_2518_);
v___x_2520_ = lean_box(v___x_2519_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2520_);
v___x_2522_ = v___x_2515_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
v_a_2525_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2512_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2512_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2533_, v_a_2534_);
lean_dec_ref(v_a_2534_);
lean_dec_ref(v_e_2533_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2537_, v_a_2538_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec_ref(v_e_2546_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2566_; 
v___x_2557_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2555_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_btrueExpr_2562_; lean_object* v___x_2564_; 
v_btrueExpr_2562_ = lean_ctor_get(v_a_2558_, 3);
lean_inc_ref(v_btrueExpr_2562_);
lean_dec(v_a_2558_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_btrueExpr_2562_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_btrueExpr_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2567_);
lean_dec_ref(v_a_2567_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2570_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2587_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2601_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2601_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2601_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
size_t v___x_2594_; size_t v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2594_ = lean_ptr_addr(v_e_2586_);
v___x_2595_ = lean_ptr_addr(v_a_2590_);
lean_dec(v_a_2590_);
v___x_2596_ = lean_usize_dec_eq(v___x_2594_, v___x_2595_);
v___x_2597_ = lean_box(v___x_2596_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2597_);
v___x_2599_ = v___x_2592_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_a_2602_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2589_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2589_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2610_, v_a_2611_);
lean_dec_ref(v_a_2611_);
lean_dec_ref(v_e_2610_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2614_, v_a_2615_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec_ref(v_e_2623_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v___x_2634_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2632_);
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_bfalseExpr_2639_; lean_object* v___x_2641_; 
v_bfalseExpr_2639_ = lean_ctor_get(v_a_2635_, 4);
lean_inc_ref(v_bfalseExpr_2639_);
lean_dec(v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_bfalseExpr_2639_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_bfalseExpr_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2644_);
lean_dec_ref(v_a_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2647_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2678_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2678_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2678_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
size_t v___x_2671_; size_t v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2671_ = lean_ptr_addr(v_e_2663_);
v___x_2672_ = lean_ptr_addr(v_a_2667_);
lean_dec(v_a_2667_);
v___x_2673_ = lean_usize_dec_eq(v___x_2671_, v___x_2672_);
v___x_2674_ = lean_box(v___x_2673_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2674_);
v___x_2676_ = v___x_2669_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2666_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2666_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2687_, v_a_2688_);
lean_dec_ref(v_a_2688_);
lean_dec_ref(v_e_2687_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2691_, v_a_2692_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec_ref(v_e_2700_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2720_; 
v___x_2711_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2709_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2720_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2720_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_natZExpr_2716_; lean_object* v___x_2718_; 
v_natZExpr_2716_ = lean_ctor_get(v_a_2712_, 2);
lean_inc_ref(v_natZExpr_2716_);
lean_dec(v_a_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v_natZExpr_2716_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_natZExpr_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2721_);
lean_dec_ref(v_a_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2724_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2740_){
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
lean_object* v_ordEqExpr_2747_; lean_object* v___x_2749_; 
v_ordEqExpr_2747_ = lean_ctor_get(v_a_2743_, 5);
lean_inc_ref(v_ordEqExpr_2747_);
lean_dec(v_a_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_ordEqExpr_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_ordEqExpr_2747_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2752_);
lean_dec_ref(v_a_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2755_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2771_){
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
lean_object* v_intExpr_2778_; lean_object* v___x_2780_; 
v_intExpr_2778_ = lean_ctor_get(v_a_2774_, 6);
lean_inc_ref(v_intExpr_2778_);
lean_dec(v_a_2774_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v_intExpr_2778_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_intExpr_2778_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2783_);
lean_dec_ref(v_a_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2786_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Meta_Sym_getIntExpr(v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2802_, lean_object* v_ctx_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v_share_2807_; lean_object* v_maxFVar_2808_; lean_object* v_proofInstInfo_2809_; lean_object* v_proofInstInfoFVar_2810_; lean_object* v_letValue_2811_; lean_object* v_inferType_2812_; lean_object* v_getLevel_2813_; lean_object* v_congrInfo_2814_; lean_object* v_defEqI_2815_; lean_object* v_extensions_2816_; lean_object* v_issues_2817_; lean_object* v_canon_2818_; lean_object* v_instanceOverrides_2819_; uint8_t v_debug_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2884_; 
v___x_2806_ = lean_st_ref_take(v_a_2804_);
v_share_2807_ = lean_ctor_get(v___x_2806_, 0);
v_maxFVar_2808_ = lean_ctor_get(v___x_2806_, 1);
v_proofInstInfo_2809_ = lean_ctor_get(v___x_2806_, 2);
v_proofInstInfoFVar_2810_ = lean_ctor_get(v___x_2806_, 3);
v_letValue_2811_ = lean_ctor_get(v___x_2806_, 4);
v_inferType_2812_ = lean_ctor_get(v___x_2806_, 5);
v_getLevel_2813_ = lean_ctor_get(v___x_2806_, 6);
v_congrInfo_2814_ = lean_ctor_get(v___x_2806_, 7);
v_defEqI_2815_ = lean_ctor_get(v___x_2806_, 8);
v_extensions_2816_ = lean_ctor_get(v___x_2806_, 9);
v_issues_2817_ = lean_ctor_get(v___x_2806_, 10);
v_canon_2818_ = lean_ctor_get(v___x_2806_, 11);
v_instanceOverrides_2819_ = lean_ctor_get(v___x_2806_, 12);
v_debug_2820_ = lean_ctor_get_uint8(v___x_2806_, sizeof(void*)*13);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2822_ = v___x_2806_;
v_isShared_2823_ = v_isSharedCheck_2884_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_instanceOverrides_2819_);
lean_inc(v_canon_2818_);
lean_inc(v_issues_2817_);
lean_inc(v_extensions_2816_);
lean_inc(v_defEqI_2815_);
lean_inc(v_congrInfo_2814_);
lean_inc(v_getLevel_2813_);
lean_inc(v_inferType_2812_);
lean_inc(v_letValue_2811_);
lean_inc(v_proofInstInfoFVar_2810_);
lean_inc(v_proofInstInfo_2809_);
lean_inc(v_maxFVar_2808_);
lean_inc(v_share_2807_);
lean_dec(v___x_2806_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2884_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_maxFVar_2808_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_proofInstInfo_2809_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_proofInstInfoFVar_2810_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v_letValue_2811_);
lean_ctor_set(v_reuseFailAlloc_2883_, 5, v_inferType_2812_);
lean_ctor_set(v_reuseFailAlloc_2883_, 6, v_getLevel_2813_);
lean_ctor_set(v_reuseFailAlloc_2883_, 7, v_congrInfo_2814_);
lean_ctor_set(v_reuseFailAlloc_2883_, 8, v_defEqI_2815_);
lean_ctor_set(v_reuseFailAlloc_2883_, 9, v_extensions_2816_);
lean_ctor_set(v_reuseFailAlloc_2883_, 10, v_issues_2817_);
lean_ctor_set(v_reuseFailAlloc_2883_, 11, v_canon_2818_);
lean_ctor_set(v_reuseFailAlloc_2883_, 12, v_instanceOverrides_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2883_, sizeof(void*)*13, v_debug_2820_);
v___x_2826_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_st_ref_put(v_a_2804_, v___x_2826_);
v___x_2828_ = lean_apply_2(v_k_2802_, v_ctx_2803_, v_share_2807_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v_maxFVar_2832_; lean_object* v_proofInstInfo_2833_; lean_object* v_proofInstInfoFVar_2834_; lean_object* v_letValue_2835_; lean_object* v_inferType_2836_; lean_object* v_getLevel_2837_; lean_object* v_congrInfo_2838_; lean_object* v_defEqI_2839_; lean_object* v_extensions_2840_; lean_object* v_issues_2841_; lean_object* v_canon_2842_; lean_object* v_instanceOverrides_2843_; uint8_t v_debug_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2854_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
v_a_2830_ = lean_ctor_get(v___x_2828_, 1);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2828_, 2);
v___x_2831_ = lean_st_ref_take(v_a_2804_);
v_maxFVar_2832_ = lean_ctor_get(v___x_2831_, 1);
v_proofInstInfo_2833_ = lean_ctor_get(v___x_2831_, 2);
v_proofInstInfoFVar_2834_ = lean_ctor_get(v___x_2831_, 3);
v_letValue_2835_ = lean_ctor_get(v___x_2831_, 4);
v_inferType_2836_ = lean_ctor_get(v___x_2831_, 5);
v_getLevel_2837_ = lean_ctor_get(v___x_2831_, 6);
v_congrInfo_2838_ = lean_ctor_get(v___x_2831_, 7);
v_defEqI_2839_ = lean_ctor_get(v___x_2831_, 8);
v_extensions_2840_ = lean_ctor_get(v___x_2831_, 9);
v_issues_2841_ = lean_ctor_get(v___x_2831_, 10);
v_canon_2842_ = lean_ctor_get(v___x_2831_, 11);
v_instanceOverrides_2843_ = lean_ctor_get(v___x_2831_, 12);
v_debug_2844_ = lean_ctor_get_uint8(v___x_2831_, sizeof(void*)*13);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; 
v_unused_2855_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2855_);
v___x_2846_ = v___x_2831_;
v_isShared_2847_ = v_isSharedCheck_2854_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_instanceOverrides_2843_);
lean_inc(v_canon_2842_);
lean_inc(v_issues_2841_);
lean_inc(v_extensions_2840_);
lean_inc(v_defEqI_2839_);
lean_inc(v_congrInfo_2838_);
lean_inc(v_getLevel_2837_);
lean_inc(v_inferType_2836_);
lean_inc(v_letValue_2835_);
lean_inc(v_proofInstInfoFVar_2834_);
lean_inc(v_proofInstInfo_2833_);
lean_inc(v_maxFVar_2832_);
lean_dec(v___x_2831_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2854_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v_a_2830_);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2830_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_maxFVar_2832_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_proofInstInfo_2833_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_proofInstInfoFVar_2834_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_letValue_2835_);
lean_ctor_set(v_reuseFailAlloc_2853_, 5, v_inferType_2836_);
lean_ctor_set(v_reuseFailAlloc_2853_, 6, v_getLevel_2837_);
lean_ctor_set(v_reuseFailAlloc_2853_, 7, v_congrInfo_2838_);
lean_ctor_set(v_reuseFailAlloc_2853_, 8, v_defEqI_2839_);
lean_ctor_set(v_reuseFailAlloc_2853_, 9, v_extensions_2840_);
lean_ctor_set(v_reuseFailAlloc_2853_, 10, v_issues_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 11, v_canon_2842_);
lean_ctor_set(v_reuseFailAlloc_2853_, 12, v_instanceOverrides_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*13, v_debug_2844_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_st_ref_put(v_a_2804_, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2829_);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v_a_2857_; lean_object* v___x_2858_; lean_object* v_maxFVar_2859_; lean_object* v_proofInstInfo_2860_; lean_object* v_proofInstInfoFVar_2861_; lean_object* v_letValue_2862_; lean_object* v_inferType_2863_; lean_object* v_getLevel_2864_; lean_object* v_congrInfo_2865_; lean_object* v_defEqI_2866_; lean_object* v_extensions_2867_; lean_object* v_issues_2868_; lean_object* v_canon_2869_; lean_object* v_instanceOverrides_2870_; uint8_t v_debug_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2881_; 
v_a_2856_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2856_);
v_a_2857_ = lean_ctor_get(v___x_2828_, 1);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2828_, 2);
v___x_2858_ = lean_st_ref_take(v_a_2804_);
v_maxFVar_2859_ = lean_ctor_get(v___x_2858_, 1);
v_proofInstInfo_2860_ = lean_ctor_get(v___x_2858_, 2);
v_proofInstInfoFVar_2861_ = lean_ctor_get(v___x_2858_, 3);
v_letValue_2862_ = lean_ctor_get(v___x_2858_, 4);
v_inferType_2863_ = lean_ctor_get(v___x_2858_, 5);
v_getLevel_2864_ = lean_ctor_get(v___x_2858_, 6);
v_congrInfo_2865_ = lean_ctor_get(v___x_2858_, 7);
v_defEqI_2866_ = lean_ctor_get(v___x_2858_, 8);
v_extensions_2867_ = lean_ctor_get(v___x_2858_, 9);
v_issues_2868_ = lean_ctor_get(v___x_2858_, 10);
v_canon_2869_ = lean_ctor_get(v___x_2858_, 11);
v_instanceOverrides_2870_ = lean_ctor_get(v___x_2858_, 12);
v_debug_2871_ = lean_ctor_get_uint8(v___x_2858_, sizeof(void*)*13);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2858_, 0);
lean_dec(v_unused_2882_);
v___x_2873_ = v___x_2858_;
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
lean_inc(v_letValue_2862_);
lean_inc(v_proofInstInfoFVar_2861_);
lean_inc(v_proofInstInfo_2860_);
lean_inc(v_maxFVar_2859_);
lean_dec(v___x_2858_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2881_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v_a_2857_);
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2857_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_maxFVar_2859_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_proofInstInfo_2860_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_proofInstInfoFVar_2861_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_letValue_2862_);
lean_ctor_set(v_reuseFailAlloc_2880_, 5, v_inferType_2863_);
lean_ctor_set(v_reuseFailAlloc_2880_, 6, v_getLevel_2864_);
lean_ctor_set(v_reuseFailAlloc_2880_, 7, v_congrInfo_2865_);
lean_ctor_set(v_reuseFailAlloc_2880_, 8, v_defEqI_2866_);
lean_ctor_set(v_reuseFailAlloc_2880_, 9, v_extensions_2867_);
lean_ctor_set(v_reuseFailAlloc_2880_, 10, v_issues_2868_);
lean_ctor_set(v_reuseFailAlloc_2880_, 11, v_canon_2869_);
lean_ctor_set(v_reuseFailAlloc_2880_, 12, v_instanceOverrides_2870_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*13, v_debug_2871_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_st_ref_put(v_a_2804_, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_a_2856_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2885_, lean_object* v_ctx_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2885_, v_ctx_2886_, v_a_2887_);
lean_dec(v_a_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2890_, lean_object* v_k_2891_, lean_object* v_ctx_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2891_, v_ctx_2892_, v_a_2894_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2901_, lean_object* v_k_2902_, lean_object* v_ctx_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2901_, v_k_2902_, v_ctx_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2912_){
_start:
{
lean_object* v_config_2913_; lean_object* v_sharedExprs_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2931_; 
v_config_2913_ = lean_ctor_get(v_ctx_2912_, 1);
v_sharedExprs_2914_ = lean_ctor_get(v_ctx_2912_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_ctx_2912_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2916_ = v_ctx_2912_;
v_isShared_2917_ = v_isSharedCheck_2931_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_config_2913_);
lean_inc(v_sharedExprs_2914_);
lean_dec(v_ctx_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2931_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
uint8_t v_verbose_2918_; uint8_t v_enforceUnfoldReducible_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2930_; 
v_verbose_2918_ = lean_ctor_get_uint8(v_config_2913_, 0);
v_enforceUnfoldReducible_2919_ = lean_ctor_get_uint8(v_config_2913_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_config_2913_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2921_ = v_config_2913_;
v_isShared_2922_ = v_isSharedCheck_2930_;
goto v_resetjp_2920_;
}
else
{
lean_dec(v_config_2913_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2930_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
uint8_t v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = 0;
if (v_isShared_2922_ == 0)
{
v___x_2925_ = v___x_2921_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2929_, 0, v_verbose_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2929_, 1, v_enforceUnfoldReducible_2919_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2927_; 
lean_ctor_set_uint8(v___x_2925_, 2, v___x_2923_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2925_);
v___x_2927_ = v___x_2916_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_sharedExprs_2914_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2933_, lean_object* v_x_2934_){
_start:
{
lean_object* v___f_2935_; lean_object* v___x_2936_; 
v___f_2935_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2936_ = lean_apply_3(v_inst_2933_, lean_box(0), v___f_2935_, v_x_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2937_, lean_object* v_00_u03b1_2938_, lean_object* v_inst_2939_, lean_object* v_x_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2939_, v_x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2942_){
_start:
{
lean_object* v_config_2943_; lean_object* v_sharedExprs_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2960_; 
v_config_2943_ = lean_ctor_get(v_ctx_2942_, 1);
v_sharedExprs_2944_ = lean_ctor_get(v_ctx_2942_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_ctx_2942_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2946_ = v_ctx_2942_;
v_isShared_2947_ = v_isSharedCheck_2960_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_config_2943_);
lean_inc(v_sharedExprs_2944_);
lean_dec(v_ctx_2942_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2960_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v_verbose_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2959_; 
v_verbose_2948_ = lean_ctor_get_uint8(v_config_2943_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_config_2943_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2950_ = v_config_2943_;
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
else
{
lean_dec(v_config_2943_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
uint8_t v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = 0;
if (v_isShared_2951_ == 0)
{
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2958_, 0, v_verbose_2948_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
lean_ctor_set_uint8(v___x_2954_, 1, v___x_2952_);
lean_ctor_set_uint8(v___x_2954_, 2, v___x_2952_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v___x_2954_);
v___x_2956_ = v___x_2946_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_sharedExprs_2944_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_2962_, lean_object* v_x_2963_){
_start:
{
lean_object* v___f_2964_; lean_object* v___x_2965_; 
v___f_2964_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_2965_ = lean_apply_3(v_inst_2962_, lean_box(0), v___f_2964_, v_x_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_2966_, lean_object* v_00_u03b1_2967_, lean_object* v_inst_2968_, lean_object* v_x_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_2968_, v_x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_config_2974_; lean_object* v___x_2975_; lean_object* v_env_2976_; uint8_t v_enforceUnfoldReducible_2977_; uint8_t v_enforceFoldProjs_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_config_2974_ = lean_ctor_get(v_a_2971_, 1);
v___x_2975_ = lean_st_ref_get(v_a_2972_);
v_env_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc_ref(v_env_2976_);
lean_dec(v___x_2975_);
v_enforceUnfoldReducible_2977_ = lean_ctor_get_uint8(v_config_2974_, 1);
v_enforceFoldProjs_2978_ = lean_ctor_get_uint8(v_config_2974_, 2);
v___x_2979_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2979_, 0, v_env_2976_);
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*1, v_enforceUnfoldReducible_2977_);
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*1 + 1, v_enforceFoldProjs_2978_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2985_, v_a_2990_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_config_3008_; uint8_t v_enforceUnfoldReducible_3009_; uint8_t v_enforceFoldProjs_3010_; lean_object* v_e_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v_e_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; 
v_config_3008_ = lean_ctor_get(v_a_3002_, 1);
v_enforceUnfoldReducible_3009_ = lean_ctor_get_uint8(v_config_3008_, 1);
v_enforceFoldProjs_3010_ = lean_ctor_get_uint8(v_config_3008_, 2);
if (v_enforceUnfoldReducible_3009_ == 0)
{
v_e_3020_ = v_e_3001_;
v___y_3021_ = v_a_3003_;
v___y_3022_ = v_a_3004_;
v___y_3023_ = v_a_3005_;
v___y_3024_ = v_a_3006_;
goto v___jp_3019_;
}
else
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3001_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v_e_3020_ = v_a_3028_;
v___y_3021_ = v_a_3003_;
v___y_3022_ = v_a_3004_;
v___y_3023_ = v_a_3005_;
v___y_3024_ = v_a_3006_;
goto v___jp_3019_;
}
else
{
return v___x_3027_;
}
}
v___jp_3011_:
{
if (v_enforceUnfoldReducible_3009_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_e_3012_);
return v___x_3017_;
}
else
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
return v___x_3018_;
}
}
v___jp_3019_:
{
if (v_enforceFoldProjs_3010_ == 0)
{
v_e_3012_ = v_e_3020_;
v___y_3013_ = v___y_3021_;
v___y_3014_ = v___y_3022_;
v___y_3015_ = v___y_3023_;
v___y_3016_ = v___y_3024_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_Meta_Sym_foldProjs(v_e_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v_e_3012_ = v_a_3026_;
v___y_3013_ = v___y_3021_;
v___y_3014_ = v___y_3022_;
v___y_3015_ = v___y_3023_;
v___y_3016_ = v___y_3024_;
goto v___jp_3011_;
}
else
{
return v___x_3025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec_ref(v_a_3030_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3037_, v_a_3038_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
return v_res_3054_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_instMonadEIO___redArg();
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v_toApplicative_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3133_; 
v___x_3068_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3069_ = l_StateRefT_x27_instMonad___redArg(v___x_3068_);
v_toApplicative_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_3069_, 1);
lean_dec(v_unused_3134_);
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3133_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_toApplicative_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3133_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_toFunctor_3074_; lean_object* v_toSeq_3075_; lean_object* v_toSeqLeft_3076_; lean_object* v_toSeqRight_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3131_; 
v_toFunctor_3074_ = lean_ctor_get(v_toApplicative_3070_, 0);
v_toSeq_3075_ = lean_ctor_get(v_toApplicative_3070_, 2);
v_toSeqLeft_3076_ = lean_ctor_get(v_toApplicative_3070_, 3);
v_toSeqRight_3077_ = lean_ctor_get(v_toApplicative_3070_, 4);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_toApplicative_3070_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v_toApplicative_3070_, 1);
lean_dec(v_unused_3132_);
v___x_3079_ = v_toApplicative_3070_;
v_isShared_3080_ = v_isSharedCheck_3131_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_toSeqRight_3077_);
lean_inc(v_toSeqLeft_3076_);
lean_inc(v_toSeq_3075_);
lean_inc(v_toFunctor_3074_);
lean_dec(v_toApplicative_3070_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3131_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___f_3081_; lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___x_3090_; 
v___f_3081_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3082_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3074_);
v___f_3083_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3083_, 0, v_toFunctor_3074_);
v___f_3084_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3084_, 0, v_toFunctor_3074_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___f_3083_);
lean_ctor_set(v___x_3085_, 1, v___f_3084_);
v___f_3086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3086_, 0, v_toSeqRight_3077_);
v___f_3087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3087_, 0, v_toSeqLeft_3076_);
v___f_3088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3088_, 0, v_toSeq_3075_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 4, v___f_3086_);
lean_ctor_set(v___x_3079_, 3, v___f_3087_);
lean_ctor_set(v___x_3079_, 2, v___f_3088_);
lean_ctor_set(v___x_3079_, 1, v___f_3081_);
lean_ctor_set(v___x_3079_, 0, v___x_3085_);
v___x_3090_ = v___x_3079_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___f_3081_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v___f_3088_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v___f_3087_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v___f_3086_);
v___x_3090_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v___f_3082_);
lean_ctor_set(v___x_3072_, 0, v___x_3090_);
v___x_3092_ = v___x_3072_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___f_3082_);
v___x_3092_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3093_; lean_object* v_toApplicative_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3127_; 
v___x_3093_ = l_StateRefT_x27_instMonad___redArg(v___x_3092_);
v_toApplicative_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3093_, 1);
lean_dec(v_unused_3128_);
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3127_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_toApplicative_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3127_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_toFunctor_3098_; lean_object* v_toSeq_3099_; lean_object* v_toSeqLeft_3100_; lean_object* v_toSeqRight_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3125_; 
v_toFunctor_3098_ = lean_ctor_get(v_toApplicative_3094_, 0);
v_toSeq_3099_ = lean_ctor_get(v_toApplicative_3094_, 2);
v_toSeqLeft_3100_ = lean_ctor_get(v_toApplicative_3094_, 3);
v_toSeqRight_3101_ = lean_ctor_get(v_toApplicative_3094_, 4);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_toApplicative_3094_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_toApplicative_3094_, 1);
lean_dec(v_unused_3126_);
v___x_3103_ = v_toApplicative_3094_;
v_isShared_3104_ = v_isSharedCheck_3125_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_toSeqRight_3101_);
lean_inc(v_toSeqLeft_3100_);
lean_inc(v_toSeq_3099_);
lean_inc(v_toFunctor_3098_);
lean_dec(v_toApplicative_3094_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3125_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___f_3105_; lean_object* v___f_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___f_3110_; lean_object* v___f_3111_; lean_object* v___f_3112_; lean_object* v___x_3114_; 
v___f_3105_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3106_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3098_);
v___f_3107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3107_, 0, v_toFunctor_3098_);
v___f_3108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3108_, 0, v_toFunctor_3098_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___f_3107_);
lean_ctor_set(v___x_3109_, 1, v___f_3108_);
v___f_3110_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3110_, 0, v_toSeqRight_3101_);
v___f_3111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3111_, 0, v_toSeqLeft_3100_);
v___f_3112_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3112_, 0, v_toSeq_3099_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 4, v___f_3110_);
lean_ctor_set(v___x_3103_, 3, v___f_3111_);
lean_ctor_set(v___x_3103_, 2, v___f_3112_);
lean_ctor_set(v___x_3103_, 1, v___f_3105_);
lean_ctor_set(v___x_3103_, 0, v___x_3109_);
v___x_3114_ = v___x_3103_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___f_3105_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v___f_3112_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v___f_3111_);
lean_ctor_set(v_reuseFailAlloc_3124_, 4, v___f_3110_);
v___x_3114_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v___f_3106_);
lean_ctor_set(v___x_3096_, 0, v___x_3114_);
v___x_3116_ = v___x_3096_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___f_3106_);
v___x_3116_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___x_922__overap_3121_; lean_object* v___x_3122_; 
v___x_3117_ = l_StateRefT_x27_instMonad___redArg(v___x_3116_);
v___x_3118_ = l_Lean_instInhabitedExpr;
v___x_3119_ = l_instInhabitedOfMonad___redArg(v___x_3117_, v___x_3118_);
v___f_3120_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3120_, 0, v___x_3119_);
v___x_922__overap_3121_ = lean_panic_fn_borrowed(v___f_3120_, v_msg_3060_);
lean_dec_ref(v___f_3120_);
lean_inc(v___y_3066_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3063_);
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
v___x_3122_ = lean_apply_7(v___x_922__overap_3121_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, lean_box(0));
return v___x_3122_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3144_, lean_object* v_vals_3145_, lean_object* v_i_3146_, lean_object* v_k_3147_){
_start:
{
lean_object* v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = lean_array_get_size(v_keys_3144_);
v___x_3149_ = lean_nat_dec_lt(v_i_3146_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
lean_dec(v_i_3146_);
v___x_3150_ = lean_box(0);
return v___x_3150_;
}
else
{
lean_object* v_k_x27_3151_; uint8_t v___x_3152_; 
v_k_x27_3151_ = lean_array_fget_borrowed(v_keys_3144_, v_i_3146_);
v___x_3152_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3147_, v_k_x27_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v_i_3146_, v___x_3153_);
lean_dec(v_i_3146_);
v_i_3146_ = v___x_3154_;
goto _start;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = lean_array_fget_borrowed(v_vals_3145_, v_i_3146_);
lean_dec(v_i_3146_);
lean_inc(v___x_3156_);
lean_inc(v_k_x27_3151_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_k_x27_3151_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3159_, lean_object* v_vals_3160_, lean_object* v_i_3161_, lean_object* v_k_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3159_, v_vals_3160_, v_i_3161_, v_k_3162_);
lean_dec_ref(v_k_3162_);
lean_dec_ref(v_vals_3160_);
lean_dec_ref(v_keys_3159_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3164_, size_t v_x_3165_, lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3164_) == 0)
{
lean_object* v_es_3167_; lean_object* v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v_j_3171_; lean_object* v___x_3172_; 
v_es_3167_ = lean_ctor_get(v_x_3164_, 0);
v___x_3168_ = lean_box(2);
v___x_3169_ = ((size_t)31ULL);
v___x_3170_ = lean_usize_land(v_x_3165_, v___x_3169_);
v_j_3171_ = lean_usize_to_nat(v___x_3170_);
v___x_3172_ = lean_array_get_borrowed(v___x_3168_, v_es_3167_, v_j_3171_);
lean_dec(v_j_3171_);
switch(lean_obj_tag(v___x_3172_))
{
case 0:
{
lean_object* v_key_3173_; lean_object* v_val_3174_; uint8_t v___x_3175_; 
v_key_3173_ = lean_ctor_get(v___x_3172_, 0);
v_val_3174_ = lean_ctor_get(v___x_3172_, 1);
v___x_3175_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3166_, v_key_3173_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_box(0);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_inc(v_val_3174_);
lean_inc(v_key_3173_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_key_3173_);
lean_ctor_set(v___x_3177_, 1, v_val_3174_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
case 1:
{
lean_object* v_node_3179_; size_t v___x_3180_; size_t v___x_3181_; 
v_node_3179_ = lean_ctor_get(v___x_3172_, 0);
v___x_3180_ = ((size_t)5ULL);
v___x_3181_ = lean_usize_shift_right(v_x_3165_, v___x_3180_);
v_x_3164_ = v_node_3179_;
v_x_3165_ = v___x_3181_;
goto _start;
}
default: 
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_box(0);
return v___x_3183_;
}
}
}
else
{
lean_object* v_ks_3184_; lean_object* v_vs_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_ks_3184_ = lean_ctor_get(v_x_3164_, 0);
v_vs_3185_ = lean_ctor_get(v_x_3164_, 1);
v___x_3186_ = lean_unsigned_to_nat(0u);
v___x_3187_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3184_, v_vs_3185_, v___x_3186_, v_x_3166_);
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3188_, lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
size_t v_x_1244__boxed_3191_; lean_object* v_res_3192_; 
v_x_1244__boxed_3191_ = lean_unbox_usize(v_x_3189_);
lean_dec(v_x_3189_);
v_res_3192_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3188_, v_x_1244__boxed_3191_, v_x_3190_);
lean_dec_ref(v_x_3190_);
lean_dec_ref(v_x_3188_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3193_, lean_object* v_x_3194_){
_start:
{
uint64_t v___x_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3194_);
v___x_3196_ = lean_uint64_to_usize(v___x_3195_);
v___x_3197_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3193_, v___x_3196_, v_x_3194_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3198_, v_x_3199_);
lean_dec_ref(v_x_3199_);
lean_dec_ref(v_x_3198_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3201_, lean_object* v_cache_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3204_, v_e_3201_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_cache_3202_);
lean_ctor_set(v___x_3206_, 1, v___y_3204_);
v___x_3207_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3201_, v___y_3203_, v___x_3206_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3217_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 1);
v_a_3209_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3211_ = v___x_3207_;
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3208_);
lean_inc(v_a_3209_);
lean_dec(v___x_3207_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_set_3213_; lean_object* v___x_3215_; 
v_set_3213_ = lean_ctor_get(v_a_3208_, 1);
lean_inc_ref(v_set_3213_);
lean_dec(v_a_3208_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v_set_3213_);
v___x_3215_ = v___x_3211_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3209_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_set_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3227_; 
v_a_3218_ = lean_ctor_get(v___x_3207_, 1);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3207_, 0);
lean_dec(v_unused_3228_);
v___x_3220_ = v___x_3207_;
v_isShared_3221_ = v_isSharedCheck_3227_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3207_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3227_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v_map_3222_; lean_object* v_set_3223_; lean_object* v___x_3225_; 
v_map_3222_ = lean_ctor_get(v_a_3218_, 0);
lean_inc_ref(v_map_3222_);
v_set_3223_ = lean_ctor_get(v_a_3218_, 1);
lean_inc_ref(v_set_3223_);
lean_dec(v_a_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v_set_3223_);
lean_ctor_set(v___x_3220_, 0, v_map_3222_);
v___x_3225_ = v___x_3220_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_map_3222_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_set_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_val_3229_; lean_object* v_fst_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_cache_3202_);
lean_dec_ref(v_e_3201_);
v_val_3229_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3205_, 1);
v_fst_3230_ = lean_ctor_get(v_val_3229_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_val_3229_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v_val_3229_, 1);
lean_dec(v_unused_3238_);
v___x_3232_ = v_val_3229_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_fst_3230_);
lean_dec(v_val_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 1, v___y_3204_);
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_fst_3230_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___y_3204_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3239_, lean_object* v_cache_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3239_, v_cache_3240_, v___y_3241_, v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3243_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3246_ = lean_unsigned_to_nat(16u);
v___x_3247_ = lean_unsigned_to_nat(401u);
v___x_3248_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3249_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_3250_ = l_mkPanicMessageWithDecl(v___x_3249_, v___x_3248_, v___x_3247_, v___x_3246_, v___x_3245_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3251_, lean_object* v_cache_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v___f_3260_; lean_object* v___x_3261_; lean_object* v_env_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3276_; 
v___f_3260_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3260_, 0, v_e_3251_);
lean_closure_set(v___f_3260_, 1, v_cache_3252_);
v___x_3261_ = lean_st_ref_get(v_a_3258_);
v_env_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc_ref(v_env_3262_);
lean_dec(v___x_3261_);
v___x_3263_ = 0;
v___x_3264_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3264_, 0, v_env_3262_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*1, v___x_3263_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*1 + 1, v___x_3263_);
v___x_3265_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3260_, v___x_3264_, v_a_3254_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3276_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3276_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
if (lean_obj_tag(v_a_3266_) == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec_ref_known(v_a_3266_, 1);
lean_del_object(v___x_3268_);
v___x_3270_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3271_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3270_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
return v___x_3271_;
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; 
v_a_3272_ = lean_ctor_get(v_a_3266_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v_a_3266_, 1);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v_a_3272_);
v___x_3274_ = v___x_3268_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3272_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3277_, lean_object* v_cache_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3277_, v_cache_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3288_, v_x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3291_, lean_object* v_x_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3291_, v_x_3292_, v_x_3293_);
lean_dec_ref(v_x_3293_);
lean_dec_ref(v_x_3292_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, size_t v_x_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3296_, v_x_3297_, v_x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_, lean_object* v_x_3303_){
_start:
{
size_t v_x_1449__boxed_3304_; lean_object* v_res_3305_; 
v_x_1449__boxed_3304_ = lean_unbox_usize(v_x_3302_);
lean_dec(v_x_3302_);
v_res_3305_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3300_, v_x_3301_, v_x_1449__boxed_3304_, v_x_3303_);
lean_dec_ref(v_x_3303_);
lean_dec_ref(v_x_3301_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3306_, lean_object* v_keys_3307_, lean_object* v_vals_3308_, lean_object* v_heq_3309_, lean_object* v_i_3310_, lean_object* v_k_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3307_, v_vals_3308_, v_i_3310_, v_k_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_keys_3314_, lean_object* v_vals_3315_, lean_object* v_heq_3316_, lean_object* v_i_3317_, lean_object* v_k_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3313_, v_keys_3314_, v_vals_3315_, v_heq_3316_, v_i_3317_, v_k_3318_);
lean_dec_ref(v_k_3318_);
lean_dec_ref(v_vals_3315_);
lean_dec_ref(v_keys_3314_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg(lean_object* v_e_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v_share_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_st_ref_get(v_a_3321_);
v_share_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc_ref(v_share_3324_);
lean_dec(v___x_3323_);
v___x_3325_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_share_3324_, v_e_3320_);
lean_dec_ref(v_share_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = 0;
v___x_3327_ = lean_box(v___x_3326_);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
return v___x_3328_;
}
else
{
lean_object* v_val_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3341_; 
v_val_3329_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3331_ = v___x_3325_;
v_isShared_3332_ = v_isSharedCheck_3341_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_val_3329_);
lean_dec(v___x_3325_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3341_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_fst_3333_; size_t v___x_3334_; size_t v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v_fst_3333_ = lean_ctor_get(v_val_3329_, 0);
lean_inc(v_fst_3333_);
lean_dec(v_val_3329_);
v___x_3334_ = lean_ptr_addr(v_fst_3333_);
lean_dec(v_fst_3333_);
v___x_3335_ = lean_ptr_addr(v_e_3320_);
v___x_3336_ = lean_usize_dec_eq(v___x_3334_, v___x_3335_);
v___x_3337_ = lean_box(v___x_3336_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3337_);
v___x_3339_ = v___x_3331_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___redArg___boxed(lean_object* v_e_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_e_3342_, v_a_3343_);
lean_dec(v_a_3343_);
lean_dec_ref(v_e_3342_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared(lean_object* v_e_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_e_3346_, v_a_3348_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isMaxShared___boxed(lean_object* v_e_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Meta_Sym_isMaxShared(v_e_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec_ref(v_e_3355_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_ref_3370_; lean_object* v___x_3371_; lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3380_; 
v_ref_3370_ = lean_ctor_get(v___y_3367_, 2);
v___x_3371_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_inc(v_ref_3370_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v_ref_3370_);
lean_ctor_set(v___x_3376_, 1, v_a_3372_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 1);
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3391_, lean_object* v_cache_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___x_3410_; 
v___x_3410_ = l_Lean_Expr_hasLooseBVars(v_e_3391_);
if (v___x_3410_ == 0)
{
v___y_3401_ = v_a_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
v___y_3405_ = v_a_3397_;
v___y_3406_ = v_a_3398_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v_cache_3392_);
v___x_3411_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3412_ = l_Lean_indentExpr(v_e_3391_);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3413_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
v___jp_3400_:
{
lean_object* v___x_3407_; 
v___x_3407_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3391_, v___y_3401_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v___x_3409_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3408_, v_cache_3392_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3409_;
}
else
{
lean_dec_ref(v_cache_3392_);
return v___x_3407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3423_, lean_object* v_cache_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3423_, v_cache_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3433_, lean_object* v_msg_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3434_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3443_, lean_object* v_msg_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3443_, v_msg_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3453_, lean_object* v___x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3456_, v_e_3453_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3454_);
lean_ctor_set(v___x_3458_, 1, v___y_3456_);
v___x_3459_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3453_, v___y_3455_, v___x_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3469_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 1);
v_a_3461_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3463_ = v___x_3459_;
v_isShared_3464_ = v_isSharedCheck_3469_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3460_);
lean_inc(v_a_3461_);
lean_dec(v___x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3469_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_set_3465_; lean_object* v___x_3467_; 
v_set_3465_ = lean_ctor_get(v_a_3460_, 1);
lean_inc_ref(v_set_3465_);
lean_dec(v_a_3460_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_set_3465_);
v___x_3467_ = v___x_3463_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3461_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_set_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3479_; 
v_a_3470_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3480_);
v___x_3472_ = v___x_3459_;
v_isShared_3473_ = v_isSharedCheck_3479_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3459_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3479_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v_map_3474_; lean_object* v_set_3475_; lean_object* v___x_3477_; 
v_map_3474_ = lean_ctor_get(v_a_3470_, 0);
lean_inc_ref(v_map_3474_);
v_set_3475_ = lean_ctor_get(v_a_3470_, 1);
lean_inc_ref(v_set_3475_);
lean_dec(v_a_3470_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v_set_3475_);
lean_ctor_set(v___x_3472_, 0, v_map_3474_);
v___x_3477_ = v___x_3472_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_map_3474_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_set_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_val_3481_; lean_object* v_fst_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v___x_3454_);
lean_dec_ref(v_e_3453_);
v_val_3481_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v___x_3457_, 1);
v_fst_3482_ = lean_ctor_get(v_val_3481_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_val_3481_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v_val_3481_, 1);
lean_dec(v_unused_3490_);
v___x_3484_ = v_val_3481_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_fst_3482_);
lean_dec(v_val_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v___y_3456_);
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_fst_3482_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___y_3456_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3491_, lean_object* v___x_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3491_, v___x_3492_, v___y_3493_, v___y_3494_);
lean_dec_ref(v___y_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v___x_3504_; lean_object* v_a_3505_; lean_object* v___x_3506_; lean_object* v___f_3507_; lean_object* v___x_3508_; lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3519_; 
v___x_3504_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3497_, v_a_3502_);
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref(v___x_3504_);
v___x_3506_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3496_);
v___f_3507_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3507_, 0, v_e_3496_);
lean_closure_set(v___f_3507_, 1, v___x_3506_);
v___x_3508_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3507_, v_a_3505_, v_a_3498_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
if (lean_obj_tag(v_a_3509_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3514_; 
lean_del_object(v___x_3511_);
v_a_3513_ = lean_ctor_get(v_a_3509_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v_a_3509_, 1);
v___x_3514_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3496_, v_a_3513_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
return v___x_3514_;
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; 
lean_dec_ref(v_e_3496_);
v_a_3515_ = lean_ctor_get(v_a_3509_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v_a_3509_, 1);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v_a_3515_);
v___x_3517_ = v___x_3511_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Meta_Sym_shareCommon(v_e_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3529_, v___y_3530_, v___y_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3533_, v___y_3534_, v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___f_3545_; lean_object* v___x_3546_; lean_object* v_a_3547_; lean_object* v___x_3548_; lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3559_; 
lean_inc_ref(v_e_3537_);
v___f_3545_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3545_, 0, v_e_3537_);
v___x_3546_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3538_, v_a_3543_);
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3545_, v_a_3547_, v_a_3539_);
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
if (lean_obj_tag(v_a_3549_) == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec_ref_known(v_a_3549_, 1);
lean_del_object(v___x_3551_);
v___x_3553_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3554_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3537_, v___x_3553_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
return v___x_3554_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; 
lean_dec_ref(v_e_3537_);
v_a_3555_ = lean_ctor_get(v_a_3549_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v_a_3549_, 1);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v_a_3555_);
v___x_3557_ = v___x_3551_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3555_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3569_, lean_object* v_vals_3570_, lean_object* v_i_3571_, lean_object* v_k_3572_){
_start:
{
lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3573_ = lean_array_get_size(v_keys_3569_);
v___x_3574_ = lean_nat_dec_lt(v_i_3571_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; 
lean_dec(v_i_3571_);
v___x_3575_ = lean_box(0);
return v___x_3575_;
}
else
{
lean_object* v_k_x27_3576_; uint8_t v___x_3577_; 
v_k_x27_3576_ = lean_array_fget_borrowed(v_keys_3569_, v_i_3571_);
v___x_3577_ = l_Lean_instBEqFVarId_beq(v_k_3572_, v_k_x27_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_unsigned_to_nat(1u);
v___x_3579_ = lean_nat_add(v_i_3571_, v___x_3578_);
lean_dec(v_i_3571_);
v_i_3571_ = v___x_3579_;
goto _start;
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = lean_array_fget_borrowed(v_vals_3570_, v_i_3571_);
lean_dec(v_i_3571_);
lean_inc(v___x_3581_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3583_, lean_object* v_vals_3584_, lean_object* v_i_3585_, lean_object* v_k_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3583_, v_vals_3584_, v_i_3585_, v_k_3586_);
lean_dec(v_k_3586_);
lean_dec_ref(v_vals_3584_);
lean_dec_ref(v_keys_3583_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(lean_object* v_x_3588_, size_t v_x_3589_, lean_object* v_x_3590_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v_es_3591_; lean_object* v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; lean_object* v_j_3595_; lean_object* v___x_3596_; 
v_es_3591_ = lean_ctor_get(v_x_3588_, 0);
v___x_3592_ = lean_box(2);
v___x_3593_ = ((size_t)31ULL);
v___x_3594_ = lean_usize_land(v_x_3589_, v___x_3593_);
v_j_3595_ = lean_usize_to_nat(v___x_3594_);
v___x_3596_ = lean_array_get_borrowed(v___x_3592_, v_es_3591_, v_j_3595_);
lean_dec(v_j_3595_);
switch(lean_obj_tag(v___x_3596_))
{
case 0:
{
lean_object* v_key_3597_; lean_object* v_val_3598_; uint8_t v___x_3599_; 
v_key_3597_ = lean_ctor_get(v___x_3596_, 0);
v_val_3598_ = lean_ctor_get(v___x_3596_, 1);
v___x_3599_ = l_Lean_instBEqFVarId_beq(v_x_3590_, v_key_3597_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_box(0);
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; 
lean_inc(v_val_3598_);
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_val_3598_);
return v___x_3601_;
}
}
case 1:
{
lean_object* v_node_3602_; size_t v___x_3603_; size_t v___x_3604_; 
v_node_3602_ = lean_ctor_get(v___x_3596_, 0);
v___x_3603_ = ((size_t)5ULL);
v___x_3604_ = lean_usize_shift_right(v_x_3589_, v___x_3603_);
v_x_3588_ = v_node_3602_;
v_x_3589_ = v___x_3604_;
goto _start;
}
default: 
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_box(0);
return v___x_3606_;
}
}
}
else
{
lean_object* v_ks_3607_; lean_object* v_vs_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_ks_3607_ = lean_ctor_get(v_x_3588_, 0);
v_vs_3608_ = lean_ctor_get(v_x_3588_, 1);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3607_, v_vs_3608_, v___x_3609_, v_x_3590_);
return v___x_3610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
size_t v_x_4130__boxed_3614_; lean_object* v_res_3615_; 
v_x_4130__boxed_3614_ = lean_unbox_usize(v_x_3612_);
lean_dec(v_x_3612_);
v_res_3615_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3611_, v_x_4130__boxed_3614_, v_x_3613_);
lean_dec(v_x_3613_);
lean_dec_ref(v_x_3611_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
uint64_t v___x_3618_; size_t v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = l_Lean_instHashableFVarId_hash(v_x_3617_);
v___x_3619_ = lean_uint64_to_usize(v___x_3618_);
v___x_3620_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3616_, v___x_3619_, v_x_3617_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg___boxed(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_x_3621_, v_x_3622_);
lean_dec(v_x_3622_);
lean_dec_ref(v_x_3621_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v_ks_3628_; lean_object* v_vs_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3653_; 
v_ks_3628_ = lean_ctor_get(v_x_3624_, 0);
v_vs_3629_ = lean_ctor_get(v_x_3624_, 1);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_x_3624_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3631_ = v_x_3624_;
v_isShared_3632_ = v_isSharedCheck_3653_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_vs_3629_);
lean_inc(v_ks_3628_);
lean_dec(v_x_3624_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3653_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3633_ = lean_array_get_size(v_ks_3628_);
v___x_3634_ = lean_nat_dec_lt(v_x_3625_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_dec(v_x_3625_);
v___x_3635_ = lean_array_push(v_ks_3628_, v_x_3626_);
v___x_3636_ = lean_array_push(v_vs_3629_, v_x_3627_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3636_);
lean_ctor_set(v___x_3631_, 0, v___x_3635_);
v___x_3638_ = v___x_3631_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
else
{
lean_object* v_k_x27_3640_; uint8_t v___x_3641_; 
v_k_x27_3640_ = lean_array_fget_borrowed(v_ks_3628_, v_x_3625_);
v___x_3641_ = l_Lean_instBEqFVarId_beq(v_x_3626_, v_k_x27_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3643_; 
if (v_isShared_3632_ == 0)
{
v___x_3643_ = v___x_3631_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_ks_3628_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_vs_3629_);
v___x_3643_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = lean_unsigned_to_nat(1u);
v___x_3645_ = lean_nat_add(v_x_3625_, v___x_3644_);
lean_dec(v_x_3625_);
v_x_3624_ = v___x_3643_;
v_x_3625_ = v___x_3645_;
goto _start;
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3648_ = lean_array_fset(v_ks_3628_, v_x_3625_, v_x_3626_);
v___x_3649_ = lean_array_fset(v_vs_3629_, v_x_3625_, v_x_3627_);
lean_dec(v_x_3625_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3649_);
lean_ctor_set(v___x_3631_, 0, v___x_3648_);
v___x_3651_ = v___x_3631_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_3654_, lean_object* v_k_3655_, lean_object* v_v_3656_){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_3654_, v___x_3657_, v_k_3655_, v_v_3656_);
return v___x_3658_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(lean_object* v_x_3660_, size_t v_x_3661_, size_t v_x_3662_, lean_object* v_x_3663_, lean_object* v_x_3664_){
_start:
{
if (lean_obj_tag(v_x_3660_) == 0)
{
lean_object* v_es_3665_; size_t v___x_3666_; size_t v___x_3667_; lean_object* v_j_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v_es_3665_ = lean_ctor_get(v_x_3660_, 0);
v___x_3666_ = ((size_t)31ULL);
v___x_3667_ = lean_usize_land(v_x_3661_, v___x_3666_);
v_j_3668_ = lean_usize_to_nat(v___x_3667_);
v___x_3669_ = lean_array_get_size(v_es_3665_);
v___x_3670_ = lean_nat_dec_lt(v_j_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_dec(v_j_3668_);
lean_dec(v_x_3664_);
lean_dec(v_x_3663_);
return v_x_3660_;
}
else
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3709_; 
lean_inc_ref(v_es_3665_);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_x_3660_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_x_3660_, 0);
lean_dec(v_unused_3710_);
v___x_3672_ = v_x_3660_;
v_isShared_3673_ = v_isSharedCheck_3709_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v_x_3660_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3709_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_v_3674_; lean_object* v___x_3675_; lean_object* v_xs_x27_3676_; lean_object* v___y_3678_; 
v_v_3674_ = lean_array_fget(v_es_3665_, v_j_3668_);
v___x_3675_ = lean_box(0);
v_xs_x27_3676_ = lean_array_fset(v_es_3665_, v_j_3668_, v___x_3675_);
switch(lean_obj_tag(v_v_3674_))
{
case 0:
{
lean_object* v_key_3683_; lean_object* v_val_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3694_; 
v_key_3683_ = lean_ctor_get(v_v_3674_, 0);
v_val_3684_ = lean_ctor_get(v_v_3674_, 1);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_v_3674_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3686_ = v_v_3674_;
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_val_3684_);
lean_inc(v_key_3683_);
lean_dec(v_v_3674_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
uint8_t v___x_3688_; 
v___x_3688_ = l_Lean_instBEqFVarId_beq(v_x_3663_, v_key_3683_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_del_object(v___x_3686_);
v___x_3689_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3683_, v_val_3684_, v_x_3663_, v_x_3664_);
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
v___y_3678_ = v___x_3690_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3692_; 
lean_dec(v_val_3684_);
lean_dec(v_key_3683_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v_x_3664_);
lean_ctor_set(v___x_3686_, 0, v_x_3663_);
v___x_3692_ = v___x_3686_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_x_3663_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_x_3664_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
v___y_3678_ = v___x_3692_;
goto v___jp_3677_;
}
}
}
}
case 1:
{
lean_object* v_node_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3707_; 
v_node_3695_ = lean_ctor_get(v_v_3674_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_v_3674_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3697_ = v_v_3674_;
v_isShared_3698_ = v_isSharedCheck_3707_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_node_3695_);
lean_dec(v_v_3674_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3707_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
size_t v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; size_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3699_ = ((size_t)5ULL);
v___x_3700_ = lean_usize_shift_right(v_x_3661_, v___x_3699_);
v___x_3701_ = ((size_t)1ULL);
v___x_3702_ = lean_usize_add(v_x_3662_, v___x_3701_);
v___x_3703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_node_3695_, v___x_3700_, v___x_3702_, v_x_3663_, v_x_3664_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3703_);
v___x_3705_ = v___x_3697_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
v___y_3678_ = v___x_3705_;
goto v___jp_3677_;
}
}
}
default: 
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3708_, 0, v_x_3663_);
lean_ctor_set(v___x_3708_, 1, v_x_3664_);
v___y_3678_ = v___x_3708_;
goto v___jp_3677_;
}
}
v___jp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = lean_array_fset(v_xs_x27_3676_, v_j_3668_, v___y_3678_);
lean_dec(v_j_3668_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3679_);
v___x_3681_ = v___x_3672_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
else
{
lean_object* v_ks_3711_; lean_object* v_vs_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3730_; 
v_ks_3711_ = lean_ctor_get(v_x_3660_, 0);
v_vs_3712_ = lean_ctor_get(v_x_3660_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_x_3660_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3714_ = v_x_3660_;
v_isShared_3715_ = v_isSharedCheck_3730_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_vs_3712_);
lean_inc(v_ks_3711_);
lean_dec(v_x_3660_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3730_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_ks_3711_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_vs_3712_);
v___x_3717_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v_newNode_3718_; size_t v___x_3719_; uint8_t v___x_3720_; 
v_newNode_3718_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(v___x_3717_, v_x_3663_, v_x_3664_);
v___x_3719_ = ((size_t)7ULL);
v___x_3720_ = lean_usize_dec_le(v___x_3719_, v_x_3662_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3721_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3718_);
v___x_3722_ = lean_unsigned_to_nat(4u);
v___x_3723_ = lean_nat_dec_lt(v___x_3721_, v___x_3722_);
lean_dec(v___x_3721_);
if (v___x_3723_ == 0)
{
lean_object* v_ks_3724_; lean_object* v_vs_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_ks_3724_ = lean_ctor_get(v_newNode_3718_, 0);
lean_inc_ref(v_ks_3724_);
v_vs_3725_ = lean_ctor_get(v_newNode_3718_, 1);
lean_inc_ref(v_vs_3725_);
lean_dec_ref(v_newNode_3718_);
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0);
v___x_3728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_x_3662_, v_ks_3724_, v_vs_3725_, v___x_3726_, v___x_3727_);
lean_dec_ref(v_vs_3725_);
lean_dec_ref(v_ks_3724_);
return v___x_3728_;
}
else
{
return v_newNode_3718_;
}
}
else
{
return v_newNode_3718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_3731_, lean_object* v_keys_3732_, lean_object* v_vals_3733_, lean_object* v_i_3734_, lean_object* v_entries_3735_){
_start:
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = lean_array_get_size(v_keys_3732_);
v___x_3737_ = lean_nat_dec_lt(v_i_3734_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_dec(v_i_3734_);
return v_entries_3735_;
}
else
{
lean_object* v_k_3738_; lean_object* v_v_3739_; uint64_t v___x_3740_; size_t v_h_3741_; size_t v___x_3742_; lean_object* v___x_3743_; size_t v___x_3744_; size_t v___x_3745_; size_t v___x_3746_; size_t v_h_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_k_3738_ = lean_array_fget_borrowed(v_keys_3732_, v_i_3734_);
v_v_3739_ = lean_array_fget_borrowed(v_vals_3733_, v_i_3734_);
v___x_3740_ = l_Lean_instHashableFVarId_hash(v_k_3738_);
v_h_3741_ = lean_uint64_to_usize(v___x_3740_);
v___x_3742_ = ((size_t)5ULL);
v___x_3743_ = lean_unsigned_to_nat(1u);
v___x_3744_ = ((size_t)1ULL);
v___x_3745_ = lean_usize_sub(v_depth_3731_, v___x_3744_);
v___x_3746_ = lean_usize_mul(v___x_3742_, v___x_3745_);
v_h_3747_ = lean_usize_shift_right(v_h_3741_, v___x_3746_);
v___x_3748_ = lean_nat_add(v_i_3734_, v___x_3743_);
lean_dec(v_i_3734_);
lean_inc(v_v_3739_);
lean_inc(v_k_3738_);
v___x_3749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_entries_3735_, v_h_3747_, v_depth_3731_, v_k_3738_, v_v_3739_);
v_i_3734_ = v___x_3748_;
v_entries_3735_ = v___x_3749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_3751_, lean_object* v_keys_3752_, lean_object* v_vals_3753_, lean_object* v_i_3754_, lean_object* v_entries_3755_){
_start:
{
size_t v_depth_boxed_3756_; lean_object* v_res_3757_; 
v_depth_boxed_3756_ = lean_unbox_usize(v_depth_3751_);
lean_dec(v_depth_3751_);
v_res_3757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_3756_, v_keys_3752_, v_vals_3753_, v_i_3754_, v_entries_3755_);
lean_dec_ref(v_vals_3753_);
lean_dec_ref(v_keys_3752_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_3758_, lean_object* v_x_3759_, lean_object* v_x_3760_, lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
size_t v_x_4265__boxed_3763_; size_t v_x_4266__boxed_3764_; lean_object* v_res_3765_; 
v_x_4265__boxed_3763_ = lean_unbox_usize(v_x_3759_);
lean_dec(v_x_3759_);
v_x_4266__boxed_3764_ = lean_unbox_usize(v_x_3760_);
lean_dec(v_x_3760_);
v_res_3765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3758_, v_x_4265__boxed_3763_, v_x_4266__boxed_3764_, v_x_3761_, v_x_3762_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(lean_object* v_x_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_){
_start:
{
uint64_t v___x_3769_; size_t v___x_3770_; size_t v___x_3771_; lean_object* v___x_3772_; 
v___x_3769_ = l_Lean_instHashableFVarId_hash(v_x_3767_);
v___x_3770_ = lean_uint64_to_usize(v___x_3769_);
v___x_3771_ = ((size_t)1ULL);
v___x_3772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3766_, v___x_3770_, v___x_3771_, v_x_3767_, v_x_3768_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f(lean_object* v_fvarId_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
uint8_t v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = 0;
lean_inc(v_fvarId_3773_);
v___x_3782_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_3773_, v___x_3781_, v_a_3776_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3857_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3857_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3857_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
if (lean_obj_tag(v_a_3783_) == 1)
{
lean_object* v_val_3787_; lean_object* v___x_3788_; lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3852_; 
lean_del_object(v___x_3785_);
v_val_3787_ = lean_ctor_get(v_a_3783_, 0);
v___x_3788_ = l_Lean_Meta_Sym_isMaxShared___redArg(v_val_3787_, v_a_3775_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3852_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3852_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_unbox(v_a_3789_);
lean_dec(v_a_3789_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3847_; 
lean_inc(v_val_3787_);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v_a_3783_, 0);
lean_dec(v_unused_3848_);
v___x_3795_ = v_a_3783_;
v_isShared_3796_ = v_isSharedCheck_3847_;
goto v_resetjp_3794_;
}
else
{
lean_dec(v_a_3783_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3847_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v_letValue_3798_; lean_object* v___x_3799_; 
v___x_3797_ = lean_st_ref_get(v_a_3775_);
v_letValue_3798_ = lean_ctor_get(v___x_3797_, 4);
lean_inc_ref(v_letValue_3798_);
lean_dec(v___x_3797_);
v___x_3799_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_letValue_3798_, v_fvarId_3773_);
lean_dec_ref(v_letValue_3798_);
if (lean_obj_tag(v___x_3799_) == 1)
{
lean_object* v___x_3801_; 
lean_del_object(v___x_3795_);
lean_dec(v_val_3787_);
lean_dec(v_fvarId_3773_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3799_);
v___x_3801_ = v___x_3791_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
else
{
lean_object* v___x_3803_; 
lean_dec(v___x_3799_);
lean_del_object(v___x_3791_);
v___x_3803_ = l_Lean_Meta_Sym_shareCommon(v_val_3787_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3838_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3838_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3838_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v_share_3809_; lean_object* v_maxFVar_3810_; lean_object* v_proofInstInfo_3811_; lean_object* v_proofInstInfoFVar_3812_; lean_object* v_letValue_3813_; lean_object* v_inferType_3814_; lean_object* v_getLevel_3815_; lean_object* v_congrInfo_3816_; lean_object* v_defEqI_3817_; lean_object* v_extensions_3818_; lean_object* v_issues_3819_; lean_object* v_canon_3820_; lean_object* v_instanceOverrides_3821_; uint8_t v_debug_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3837_; 
v___x_3808_ = lean_st_ref_take(v_a_3775_);
v_share_3809_ = lean_ctor_get(v___x_3808_, 0);
v_maxFVar_3810_ = lean_ctor_get(v___x_3808_, 1);
v_proofInstInfo_3811_ = lean_ctor_get(v___x_3808_, 2);
v_proofInstInfoFVar_3812_ = lean_ctor_get(v___x_3808_, 3);
v_letValue_3813_ = lean_ctor_get(v___x_3808_, 4);
v_inferType_3814_ = lean_ctor_get(v___x_3808_, 5);
v_getLevel_3815_ = lean_ctor_get(v___x_3808_, 6);
v_congrInfo_3816_ = lean_ctor_get(v___x_3808_, 7);
v_defEqI_3817_ = lean_ctor_get(v___x_3808_, 8);
v_extensions_3818_ = lean_ctor_get(v___x_3808_, 9);
v_issues_3819_ = lean_ctor_get(v___x_3808_, 10);
v_canon_3820_ = lean_ctor_get(v___x_3808_, 11);
v_instanceOverrides_3821_ = lean_ctor_get(v___x_3808_, 12);
v_debug_3822_ = lean_ctor_get_uint8(v___x_3808_, sizeof(void*)*13);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3824_ = v___x_3808_;
v_isShared_3825_ = v_isSharedCheck_3837_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_instanceOverrides_3821_);
lean_inc(v_canon_3820_);
lean_inc(v_issues_3819_);
lean_inc(v_extensions_3818_);
lean_inc(v_defEqI_3817_);
lean_inc(v_congrInfo_3816_);
lean_inc(v_getLevel_3815_);
lean_inc(v_inferType_3814_);
lean_inc(v_letValue_3813_);
lean_inc(v_proofInstInfoFVar_3812_);
lean_inc(v_proofInstInfo_3811_);
lean_inc(v_maxFVar_3810_);
lean_inc(v_share_3809_);
lean_dec(v___x_3808_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3837_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
lean_inc(v_a_3804_);
v___x_3826_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(v_letValue_3813_, v_fvarId_3773_, v_a_3804_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 4, v___x_3826_);
v___x_3828_ = v___x_3824_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_share_3809_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_maxFVar_3810_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_proofInstInfo_3811_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_proofInstInfoFVar_3812_);
lean_ctor_set(v_reuseFailAlloc_3836_, 4, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3836_, 5, v_inferType_3814_);
lean_ctor_set(v_reuseFailAlloc_3836_, 6, v_getLevel_3815_);
lean_ctor_set(v_reuseFailAlloc_3836_, 7, v_congrInfo_3816_);
lean_ctor_set(v_reuseFailAlloc_3836_, 8, v_defEqI_3817_);
lean_ctor_set(v_reuseFailAlloc_3836_, 9, v_extensions_3818_);
lean_ctor_set(v_reuseFailAlloc_3836_, 10, v_issues_3819_);
lean_ctor_set(v_reuseFailAlloc_3836_, 11, v_canon_3820_);
lean_ctor_set(v_reuseFailAlloc_3836_, 12, v_instanceOverrides_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3836_, sizeof(void*)*13, v_debug_3822_);
v___x_3828_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = lean_st_ref_put(v_a_3775_, v___x_3828_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v_a_3804_);
v___x_3831_ = v___x_3795_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3804_);
v___x_3831_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3833_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3831_);
v___x_3833_ = v___x_3806_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_del_object(v___x_3795_);
lean_dec(v_fvarId_3773_);
v_a_3839_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3803_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3803_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
else
{
lean_object* v___x_3850_; 
lean_dec(v_fvarId_3773_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v_a_3783_);
v___x_3850_ = v___x_3791_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3783_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_dec(v_a_3783_);
lean_dec(v_fvarId_3773_);
v___x_3853_ = lean_box(0);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3853_);
v___x_3855_ = v___x_3785_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_dec(v_fvarId_3773_);
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLetValueS_x3f___boxed(lean_object* v_fvarId_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Meta_Sym_getLetValueS_x3f(v_fvarId_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(lean_object* v_00_u03b2_3867_, lean_object* v_x_3868_, lean_object* v_x_3869_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___redArg(v_x_3868_, v_x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0___boxed(lean_object* v_00_u03b2_3871_, lean_object* v_x_3872_, lean_object* v_x_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0(v_00_u03b2_3871_, v_x_3872_, v_x_3873_);
lean_dec(v_x_3873_);
lean_dec_ref(v_x_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1(lean_object* v_00_u03b2_3875_, lean_object* v_x_3876_, lean_object* v_x_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1___redArg(v_x_3876_, v_x_3877_, v_x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3880_, lean_object* v_x_3881_, size_t v_x_3882_, lean_object* v_x_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___redArg(v_x_3881_, v_x_3882_, v_x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3885_, lean_object* v_x_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_){
_start:
{
size_t v_x_4577__boxed_3889_; lean_object* v_res_3890_; 
v_x_4577__boxed_3889_ = lean_unbox_usize(v_x_3887_);
lean_dec(v_x_3887_);
v_res_3890_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0(v_00_u03b2_3885_, v_x_3886_, v_x_4577__boxed_3889_, v_x_3888_);
lean_dec(v_x_3888_);
lean_dec_ref(v_x_3886_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(lean_object* v_00_u03b2_3891_, lean_object* v_x_3892_, size_t v_x_3893_, size_t v_x_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg(v_x_3892_, v_x_3893_, v_x_3894_, v_x_3895_, v_x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3898_, lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_, lean_object* v_x_3902_, lean_object* v_x_3903_){
_start:
{
size_t v_x_4588__boxed_3904_; size_t v_x_4589__boxed_3905_; lean_object* v_res_3906_; 
v_x_4588__boxed_3904_ = lean_unbox_usize(v_x_3900_);
lean_dec(v_x_3900_);
v_x_4589__boxed_3905_ = lean_unbox_usize(v_x_3901_);
lean_dec(v_x_3901_);
v_res_3906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2(v_00_u03b2_3898_, v_x_3899_, v_x_4588__boxed_3904_, v_x_4589__boxed_3905_, v_x_3902_, v_x_3903_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3907_, lean_object* v_keys_3908_, lean_object* v_vals_3909_, lean_object* v_heq_3910_, lean_object* v_i_3911_, lean_object* v_k_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3908_, v_vals_3909_, v_i_3911_, v_k_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3914_, lean_object* v_keys_3915_, lean_object* v_vals_3916_, lean_object* v_heq_3917_, lean_object* v_i_3918_, lean_object* v_k_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3914_, v_keys_3915_, v_vals_3916_, v_heq_3917_, v_i_3918_, v_k_3919_);
lean_dec(v_k_3919_);
lean_dec_ref(v_vals_3916_);
lean_dec_ref(v_keys_3915_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3921_, lean_object* v_n_3922_, lean_object* v_k_3923_, lean_object* v_v_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4___redArg(v_n_3922_, v_k_3923_, v_v_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3926_, size_t v_depth_3927_, lean_object* v_keys_3928_, lean_object* v_vals_3929_, lean_object* v_heq_3930_, lean_object* v_i_3931_, lean_object* v_entries_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___redArg(v_depth_3927_, v_keys_3928_, v_vals_3929_, v_i_3931_, v_entries_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3934_, lean_object* v_depth_3935_, lean_object* v_keys_3936_, lean_object* v_vals_3937_, lean_object* v_heq_3938_, lean_object* v_i_3939_, lean_object* v_entries_3940_){
_start:
{
size_t v_depth_boxed_3941_; lean_object* v_res_3942_; 
v_depth_boxed_3941_ = lean_unbox_usize(v_depth_3935_);
lean_dec(v_depth_3935_);
v_res_3942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__5(v_00_u03b2_3934_, v_depth_boxed_3941_, v_keys_3936_, v_vals_3937_, v_heq_3938_, v_i_3939_, v_entries_3940_);
lean_dec_ref(v_vals_3937_);
lean_dec_ref(v_keys_3936_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3943_, lean_object* v_x_3944_, lean_object* v_x_3945_, lean_object* v_x_3946_, lean_object* v_x_3947_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3944_, v_x_3945_, v_x_3946_, v_x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Lean_Meta_Sym_share(v_e_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3967_){
_start:
{
lean_object* v___x_3969_; uint8_t v_debug_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3969_ = lean_st_ref_get(v_a_3967_);
v_debug_3970_ = lean_ctor_get_uint8(v___x_3969_, sizeof(void*)*13);
lean_dec(v___x_3969_);
v___x_3971_ = lean_box(v_debug_3970_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3973_);
lean_dec(v_a_3973_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3983_; uint8_t v_debug_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3983_ = lean_st_ref_get(v_a_3977_);
v_debug_3984_ = lean_ctor_get_uint8(v___x_3983_, sizeof(void*)*13);
lean_dec(v___x_3983_);
v___x_3985_ = lean_box(v_debug_3984_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3995_){
_start:
{
lean_object* v_config_3997_; lean_object* v___x_3998_; 
v_config_3997_ = lean_ctor_get(v_a_3995_, 1);
lean_inc_ref(v_config_3997_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v_config_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3999_);
lean_dec_ref(v_a_3999_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4002_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_Meta_Sym_getConfig(v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_4018_, lean_object* v_msg_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_ref_4025_; lean_object* v___x_4026_; lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4072_; 
v_ref_4025_ = lean_ctor_get(v___y_4022_, 2);
v___x_4026_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4029_ = v___x_4026_;
v_isShared_4030_ = v_isSharedCheck_4072_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4026_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4072_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v_traceState_4032_; lean_object* v_env_4033_; lean_object* v_nextMacroScope_4034_; lean_object* v_ngen_4035_; lean_object* v_auxDeclNGen_4036_; lean_object* v_cache_4037_; lean_object* v_recordedDeps_4038_; lean_object* v_messages_4039_; lean_object* v_infoState_4040_; lean_object* v_snapshotTasks_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4071_; 
v___x_4031_ = lean_st_ref_take(v___y_4023_);
v_traceState_4032_ = lean_ctor_get(v___x_4031_, 4);
v_env_4033_ = lean_ctor_get(v___x_4031_, 0);
v_nextMacroScope_4034_ = lean_ctor_get(v___x_4031_, 1);
v_ngen_4035_ = lean_ctor_get(v___x_4031_, 2);
v_auxDeclNGen_4036_ = lean_ctor_get(v___x_4031_, 3);
v_cache_4037_ = lean_ctor_get(v___x_4031_, 5);
v_recordedDeps_4038_ = lean_ctor_get(v___x_4031_, 6);
v_messages_4039_ = lean_ctor_get(v___x_4031_, 7);
v_infoState_4040_ = lean_ctor_get(v___x_4031_, 8);
v_snapshotTasks_4041_ = lean_ctor_get(v___x_4031_, 9);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4043_ = v___x_4031_;
v_isShared_4044_ = v_isSharedCheck_4071_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_snapshotTasks_4041_);
lean_inc(v_infoState_4040_);
lean_inc(v_messages_4039_);
lean_inc(v_recordedDeps_4038_);
lean_inc(v_cache_4037_);
lean_inc(v_traceState_4032_);
lean_inc(v_auxDeclNGen_4036_);
lean_inc(v_ngen_4035_);
lean_inc(v_nextMacroScope_4034_);
lean_inc(v_env_4033_);
lean_dec(v___x_4031_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4071_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
uint64_t v_tid_4045_; lean_object* v_traces_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4070_; 
v_tid_4045_ = lean_ctor_get_uint64(v_traceState_4032_, sizeof(void*)*1);
v_traces_4046_ = lean_ctor_get(v_traceState_4032_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_traceState_4032_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4048_ = v_traceState_4032_;
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_traces_4046_);
lean_dec(v_traceState_4032_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; double v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4050_ = lean_box(0);
v___x_4051_ = lean_box(0);
v___x_4052_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_4053_ = 0;
v___x_4054_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4055_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4055_, 0, v_cls_4018_);
lean_ctor_set(v___x_4055_, 1, v___x_4051_);
lean_ctor_set(v___x_4055_, 2, v___x_4054_);
lean_ctor_set_float(v___x_4055_, sizeof(void*)*3, v___x_4052_);
lean_ctor_set_float(v___x_4055_, sizeof(void*)*3 + 8, v___x_4052_);
lean_ctor_set_uint8(v___x_4055_, sizeof(void*)*3 + 16, v___x_4053_);
v___x_4056_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_4057_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v_a_4027_);
lean_ctor_set(v___x_4057_, 2, v___x_4056_);
lean_inc(v_ref_4025_);
v___x_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4058_, 0, v_ref_4025_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = l_Lean_PersistentArray_push___redArg(v_traces_4046_, v___x_4058_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4059_);
v___x_4061_ = v___x_4048_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4059_);
lean_ctor_set_uint64(v_reuseFailAlloc_4069_, sizeof(void*)*1, v_tid_4045_);
v___x_4061_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 4, v___x_4061_);
v___x_4063_ = v___x_4043_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_env_4033_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_nextMacroScope_4034_);
lean_ctor_set(v_reuseFailAlloc_4068_, 2, v_ngen_4035_);
lean_ctor_set(v_reuseFailAlloc_4068_, 3, v_auxDeclNGen_4036_);
lean_ctor_set(v_reuseFailAlloc_4068_, 4, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4068_, 5, v_cache_4037_);
lean_ctor_set(v_reuseFailAlloc_4068_, 6, v_recordedDeps_4038_);
lean_ctor_set(v_reuseFailAlloc_4068_, 7, v_messages_4039_);
lean_ctor_set(v_reuseFailAlloc_4068_, 8, v_infoState_4040_);
lean_ctor_set(v_reuseFailAlloc_4068_, 9, v_snapshotTasks_4041_);
v___x_4063_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4064_ = lean_st_ref_put(v___y_4023_, v___x_4063_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4050_);
v___x_4066_ = v___x_4029_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4050_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_4073_, lean_object* v_msg_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_4073_, v_msg_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4080_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_4084_; uint8_t v___x_4085_; double v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4084_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4085_ = 1;
v___x_4086_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_4087_ = lean_box(0);
v___x_4088_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_4089_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v___x_4087_);
lean_ctor_set(v___x_4089_, 2, v___x_4084_);
lean_ctor_set_float(v___x_4089_, sizeof(void*)*3, v___x_4086_);
lean_ctor_set_float(v___x_4089_, sizeof(void*)*3 + 8, v___x_4086_);
lean_ctor_set_uint8(v___x_4089_, sizeof(void*)*3 + 16, v___x_4085_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v___x_4101_; lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v_share_4104_; lean_object* v_maxFVar_4105_; lean_object* v_proofInstInfo_4106_; lean_object* v_proofInstInfoFVar_4107_; lean_object* v_letValue_4108_; lean_object* v_inferType_4109_; lean_object* v_getLevel_4110_; lean_object* v_congrInfo_4111_; lean_object* v_defEqI_4112_; lean_object* v_extensions_4113_; lean_object* v_issues_4114_; lean_object* v_canon_4115_; lean_object* v_instanceOverrides_4116_; uint8_t v_debug_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4137_; 
v___x_4101_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_4090_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref(v___x_4101_);
v___x_4103_ = lean_st_ref_take(v_a_4092_);
v_share_4104_ = lean_ctor_get(v___x_4103_, 0);
v_maxFVar_4105_ = lean_ctor_get(v___x_4103_, 1);
v_proofInstInfo_4106_ = lean_ctor_get(v___x_4103_, 2);
v_proofInstInfoFVar_4107_ = lean_ctor_get(v___x_4103_, 3);
v_letValue_4108_ = lean_ctor_get(v___x_4103_, 4);
v_inferType_4109_ = lean_ctor_get(v___x_4103_, 5);
v_getLevel_4110_ = lean_ctor_get(v___x_4103_, 6);
v_congrInfo_4111_ = lean_ctor_get(v___x_4103_, 7);
v_defEqI_4112_ = lean_ctor_get(v___x_4103_, 8);
v_extensions_4113_ = lean_ctor_get(v___x_4103_, 9);
v_issues_4114_ = lean_ctor_get(v___x_4103_, 10);
v_canon_4115_ = lean_ctor_get(v___x_4103_, 11);
v_instanceOverrides_4116_ = lean_ctor_get(v___x_4103_, 12);
v_debug_4117_ = lean_ctor_get_uint8(v___x_4103_, sizeof(void*)*13);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4119_ = v___x_4103_;
v_isShared_4120_ = v_isSharedCheck_4137_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_instanceOverrides_4116_);
lean_inc(v_canon_4115_);
lean_inc(v_issues_4114_);
lean_inc(v_extensions_4113_);
lean_inc(v_defEqI_4112_);
lean_inc(v_congrInfo_4111_);
lean_inc(v_getLevel_4110_);
lean_inc(v_inferType_4109_);
lean_inc(v_letValue_4108_);
lean_inc(v_proofInstInfoFVar_4107_);
lean_inc(v_proofInstInfo_4106_);
lean_inc(v_maxFVar_4105_);
lean_inc(v_share_4104_);
lean_dec(v___x_4103_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4137_;
goto v_resetjp_4118_;
}
v___jp_4098_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_box(0);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4121_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_4122_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_4102_);
v___x_4123_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v_a_4102_);
lean_ctor_set(v___x_4123_, 2, v___x_4122_);
v___x_4124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v_issues_4114_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 10, v___x_4124_);
v___x_4126_ = v___x_4119_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_share_4104_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_maxFVar_4105_);
lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_proofInstInfo_4106_);
lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_proofInstInfoFVar_4107_);
lean_ctor_set(v_reuseFailAlloc_4136_, 4, v_letValue_4108_);
lean_ctor_set(v_reuseFailAlloc_4136_, 5, v_inferType_4109_);
lean_ctor_set(v_reuseFailAlloc_4136_, 6, v_getLevel_4110_);
lean_ctor_set(v_reuseFailAlloc_4136_, 7, v_congrInfo_4111_);
lean_ctor_set(v_reuseFailAlloc_4136_, 8, v_defEqI_4112_);
lean_ctor_set(v_reuseFailAlloc_4136_, 9, v_extensions_4113_);
lean_ctor_set(v_reuseFailAlloc_4136_, 10, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4136_, 11, v_canon_4115_);
lean_ctor_set(v_reuseFailAlloc_4136_, 12, v_instanceOverrides_4116_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*13, v_debug_4117_);
v___x_4126_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; lean_object* v_toCold_4128_; lean_object* v_options_4129_; uint8_t v_hasTrace_4130_; 
v___x_4127_ = lean_st_ref_put(v_a_4092_, v___x_4126_);
v_toCold_4128_ = lean_ctor_get(v_a_4095_, 0);
v_options_4129_ = lean_ctor_get(v_toCold_4128_, 2);
v_hasTrace_4130_ = lean_ctor_get_uint8(v_options_4129_, sizeof(void*)*1);
if (v_hasTrace_4130_ == 0)
{
lean_dec(v_a_4102_);
goto v___jp_4098_;
}
else
{
lean_object* v_inheritedTraceOptions_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v_inheritedTraceOptions_4131_ = lean_ctor_get(v_toCold_4128_, 11);
v___x_4132_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_4133_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_4134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4131_, v_options_4129_, v___x_4133_);
if (v___x_4134_ == 0)
{
lean_dec(v_a_4102_);
goto v___jp_4098_;
}
else
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_4132_, v_a_4102_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
return v___x_4135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_Sym_reportIssue(v_msg_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_4147_, lean_object* v_msg_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_4147_, v_msg_4148_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_4157_, lean_object* v_msg_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_4157_, v_msg_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___x_4175_; lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4186_; 
v___x_4175_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4168_);
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4186_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4186_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
uint8_t v_verbose_4180_; 
v_verbose_4180_ = lean_ctor_get_uint8(v_a_4176_, 0);
lean_dec(v_a_4176_);
if (v_verbose_4180_ == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
lean_dec_ref(v_msg_4167_);
v___x_4181_ = lean_box(0);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4181_);
v___x_4183_ = v___x_4178_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
else
{
lean_object* v___x_4185_; 
lean_del_object(v___x_4178_);
v___x_4185_ = l_Lean_Meta_Sym_reportIssue(v_msg_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
return v___x_4185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
return v_res_4195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_4212_ = l_String_toRawSubstring_x27(v___x_4211_);
return v___x_4212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_4251_ = l_String_toRawSubstring_x27(v___x_4250_);
return v___x_4251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_4264_ = l_String_toRawSubstring_x27(v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_msg_4291_; lean_object* v_quotContext_4292_; lean_object* v_currMacroScope_4293_; lean_object* v_ref_4294_; lean_object* v___y_4295_; lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
lean_inc(v_s_4287_);
v___x_4310_ = l_Lean_Syntax_getKind(v_s_4287_);
v___x_4311_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4312_ = lean_name_eq(v___x_4310_, v___x_4311_);
lean_dec(v___x_4310_);
if (v___x_4312_ == 0)
{
lean_object* v_quotContext_4313_; lean_object* v_currMacroScope_4314_; lean_object* v_ref_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v_quotContext_4313_ = lean_ctor_get(v_a_4288_, 1);
v_currMacroScope_4314_ = lean_ctor_get(v_a_4288_, 2);
v_ref_4315_ = lean_ctor_get(v_a_4288_, 5);
v___x_4316_ = l_Lean_SourceInfo_fromRef(v_ref_4315_, v___x_4312_);
v___x_4317_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4318_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4319_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4316_, 8);
v___x_4320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4316_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4322_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4323_ = lean_box(0);
lean_inc_n(v_currMacroScope_4314_, 3);
lean_inc_n(v_quotContext_4313_, 3);
v___x_4324_ = l_Lean_addMacroScope(v_quotContext_4313_, v___x_4323_, v_currMacroScope_4314_);
v___x_4325_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4316_);
lean_ctor_set(v___x_4326_, 1, v___x_4322_);
lean_ctor_set(v___x_4326_, 2, v___x_4324_);
lean_ctor_set(v___x_4326_, 3, v___x_4325_);
v___x_4327_ = l_Lean_Syntax_node1(v___x_4316_, v___x_4321_, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node2(v___x_4316_, v___x_4318_, v___x_4320_, v___x_4327_);
v___x_4329_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4316_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4332_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4333_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4334_ = l_Lean_addMacroScope(v_quotContext_4313_, v___x_4333_, v_currMacroScope_4314_);
v___x_4335_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4316_);
lean_ctor_set(v___x_4336_, 1, v___x_4332_);
lean_ctor_set(v___x_4336_, 2, v___x_4334_);
lean_ctor_set(v___x_4336_, 3, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_node1(v___x_4316_, v___x_4331_, v___x_4336_);
v___x_4338_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4316_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = l_Lean_Syntax_node5(v___x_4316_, v___x_4317_, v___x_4328_, v_s_4287_, v___x_4330_, v___x_4337_, v___x_4339_);
v_msg_4291_ = v___x_4340_;
v_quotContext_4292_ = v_quotContext_4313_;
v_currMacroScope_4293_ = v_currMacroScope_4314_;
v_ref_4294_ = v_ref_4315_;
v___y_4295_ = v_a_4289_;
goto v___jp_4290_;
}
else
{
lean_object* v_quotContext_4341_; lean_object* v_currMacroScope_4342_; lean_object* v_ref_4343_; uint8_t v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v_quotContext_4341_ = lean_ctor_get(v_a_4288_, 1);
v_currMacroScope_4342_ = lean_ctor_get(v_a_4288_, 2);
v_ref_4343_ = lean_ctor_get(v_a_4288_, 5);
v___x_4344_ = 0;
v___x_4345_ = l_Lean_SourceInfo_fromRef(v_ref_4343_, v___x_4344_);
v___x_4346_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4347_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4345_);
v___x_4348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4345_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v___x_4349_ = l_Lean_Syntax_node2(v___x_4345_, v___x_4346_, v___x_4348_, v_s_4287_);
lean_inc(v_currMacroScope_4342_);
lean_inc(v_quotContext_4341_);
v_msg_4291_ = v___x_4349_;
v_quotContext_4292_ = v_quotContext_4341_;
v_currMacroScope_4293_ = v_currMacroScope_4342_;
v_ref_4294_ = v_ref_4343_;
v___y_4295_ = v_a_4289_;
goto v___jp_4290_;
}
v___jp_4290_:
{
uint8_t v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4296_ = 0;
v___x_4297_ = l_Lean_SourceInfo_fromRef(v_ref_4294_, v___x_4296_);
v___x_4298_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4299_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4300_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_4301_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_4302_ = l_Lean_addMacroScope(v_quotContext_4292_, v___x_4301_, v_currMacroScope_4293_);
v___x_4303_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_4297_, 3);
v___x_4304_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4297_);
lean_ctor_set(v___x_4304_, 1, v___x_4300_);
lean_ctor_set(v___x_4304_, 2, v___x_4302_);
lean_ctor_set(v___x_4304_, 3, v___x_4303_);
v___x_4305_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4306_ = l_Lean_Syntax_node1(v___x_4297_, v___x_4305_, v_msg_4291_);
v___x_4307_ = l_Lean_Syntax_node2(v___x_4297_, v___x_4299_, v___x_4304_, v___x_4306_);
v___x_4308_ = l_Lean_Syntax_node1(v___x_4297_, v___x_4298_, v___x_4307_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v___y_4295_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_4350_, v_a_4351_, v_a_4352_);
lean_dec_ref(v_a_4351_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4397_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_4394_);
v___x_4398_ = l_Lean_Syntax_isOfKind(v_x_4394_, v___x_4397_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_dec(v_x_4394_);
v___x_4399_ = lean_box(1);
v___x_4400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
lean_ctor_set(v___x_4400_, 1, v_a_4396_);
return v___x_4400_;
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v_a_4404_; lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
v___x_4401_ = lean_unsigned_to_nat(1u);
v___x_4402_ = l_Lean_Syntax_getArg(v_x_4394_, v___x_4401_);
lean_dec(v_x_4394_);
v___x_4403_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_4402_, v_a_4395_, v_a_4396_);
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
v_a_4405_ = lean_ctor_get(v___x_4403_, 1);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4407_ = v___x_4403_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_inc(v_a_4404_);
lean_dec(v___x_4403_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4404_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4413_, v_a_4414_, v_a_4415_);
lean_dec_ref(v_a_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4445_; 
v___x_4425_ = l_Lean_KVMap_instValueBool;
v___x_4426_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4418_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4445_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4445_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
uint8_t v_verbose_4431_; 
v_verbose_4431_ = lean_ctor_get_uint8(v_a_4427_, 0);
lean_dec(v_a_4427_);
if (v_verbose_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
lean_dec_ref(v_msg_4417_);
v___x_4432_ = lean_box(0);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4432_);
v___x_4434_ = v___x_4429_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4436_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4422_);
v___x_4437_ = l_Lean_Meta_Sym_sym_debug;
v___x_4438_ = l_Lean_Option_get___redArg(v___x_4425_, v___x_4436_, v___x_4437_);
lean_dec_ref(v___x_4436_);
v___x_4439_ = lean_unbox(v___x_4438_);
lean_dec(v___x_4438_);
if (v___x_4439_ == 0)
{
lean_object* v___x_4440_; lean_object* v___x_4442_; 
lean_dec_ref(v_msg_4417_);
v___x_4440_ = lean_box(0);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4440_);
v___x_4442_ = v___x_4429_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
else
{
lean_object* v___x_4444_; 
lean_del_object(v___x_4429_);
v___x_4444_ = l_Lean_Meta_Sym_reportIssue(v_msg_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
return v___x_4444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
return v_res_4454_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4457_ = l_String_toRawSubstring_x27(v___x_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_){
_start:
{
lean_object* v_msg_4477_; lean_object* v_quotContext_4478_; lean_object* v_currMacroScope_4479_; lean_object* v_ref_4480_; lean_object* v___y_4481_; lean_object* v___x_4496_; lean_object* v___x_4497_; uint8_t v___x_4498_; 
lean_inc(v_s_4473_);
v___x_4496_ = l_Lean_Syntax_getKind(v_s_4473_);
v___x_4497_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4498_ = lean_name_eq(v___x_4496_, v___x_4497_);
lean_dec(v___x_4496_);
if (v___x_4498_ == 0)
{
lean_object* v_quotContext_4499_; lean_object* v_currMacroScope_4500_; lean_object* v_ref_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v_quotContext_4499_ = lean_ctor_get(v_a_4474_, 1);
v_currMacroScope_4500_ = lean_ctor_get(v_a_4474_, 2);
v_ref_4501_ = lean_ctor_get(v_a_4474_, 5);
v___x_4502_ = l_Lean_SourceInfo_fromRef(v_ref_4501_, v___x_4498_);
v___x_4503_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4504_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4505_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4502_, 8);
v___x_4506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4502_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4508_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4509_ = lean_box(0);
lean_inc_n(v_currMacroScope_4500_, 3);
lean_inc_n(v_quotContext_4499_, 3);
v___x_4510_ = l_Lean_addMacroScope(v_quotContext_4499_, v___x_4509_, v_currMacroScope_4500_);
v___x_4511_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4512_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4502_);
lean_ctor_set(v___x_4512_, 1, v___x_4508_);
lean_ctor_set(v___x_4512_, 2, v___x_4510_);
lean_ctor_set(v___x_4512_, 3, v___x_4511_);
v___x_4513_ = l_Lean_Syntax_node1(v___x_4502_, v___x_4507_, v___x_4512_);
v___x_4514_ = l_Lean_Syntax_node2(v___x_4502_, v___x_4504_, v___x_4506_, v___x_4513_);
v___x_4515_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4502_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
v___x_4517_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4518_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4519_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4520_ = l_Lean_addMacroScope(v_quotContext_4499_, v___x_4519_, v_currMacroScope_4500_);
v___x_4521_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4522_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4502_);
lean_ctor_set(v___x_4522_, 1, v___x_4518_);
lean_ctor_set(v___x_4522_, 2, v___x_4520_);
lean_ctor_set(v___x_4522_, 3, v___x_4521_);
v___x_4523_ = l_Lean_Syntax_node1(v___x_4502_, v___x_4517_, v___x_4522_);
v___x_4524_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4502_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = l_Lean_Syntax_node5(v___x_4502_, v___x_4503_, v___x_4514_, v_s_4473_, v___x_4516_, v___x_4523_, v___x_4525_);
v_msg_4477_ = v___x_4526_;
v_quotContext_4478_ = v_quotContext_4499_;
v_currMacroScope_4479_ = v_currMacroScope_4500_;
v_ref_4480_ = v_ref_4501_;
v___y_4481_ = v_a_4475_;
goto v___jp_4476_;
}
else
{
lean_object* v_quotContext_4527_; lean_object* v_currMacroScope_4528_; lean_object* v_ref_4529_; uint8_t v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v_quotContext_4527_ = lean_ctor_get(v_a_4474_, 1);
v_currMacroScope_4528_ = lean_ctor_get(v_a_4474_, 2);
v_ref_4529_ = lean_ctor_get(v_a_4474_, 5);
v___x_4530_ = 0;
v___x_4531_ = l_Lean_SourceInfo_fromRef(v_ref_4529_, v___x_4530_);
v___x_4532_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4531_);
v___x_4534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4531_);
lean_ctor_set(v___x_4534_, 1, v___x_4533_);
v___x_4535_ = l_Lean_Syntax_node2(v___x_4531_, v___x_4532_, v___x_4534_, v_s_4473_);
lean_inc(v_currMacroScope_4528_);
lean_inc(v_quotContext_4527_);
v_msg_4477_ = v___x_4535_;
v_quotContext_4478_ = v_quotContext_4527_;
v_currMacroScope_4479_ = v_currMacroScope_4528_;
v_ref_4480_ = v_ref_4529_;
v___y_4481_ = v_a_4475_;
goto v___jp_4476_;
}
v___jp_4476_:
{
uint8_t v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4482_ = 0;
v___x_4483_ = l_Lean_SourceInfo_fromRef(v_ref_4480_, v___x_4482_);
v___x_4484_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4485_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4486_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4487_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4488_ = l_Lean_addMacroScope(v_quotContext_4478_, v___x_4487_, v_currMacroScope_4479_);
v___x_4489_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4483_, 3);
v___x_4490_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4483_);
lean_ctor_set(v___x_4490_, 1, v___x_4486_);
lean_ctor_set(v___x_4490_, 2, v___x_4488_);
lean_ctor_set(v___x_4490_, 3, v___x_4489_);
v___x_4491_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4492_ = l_Lean_Syntax_node1(v___x_4483_, v___x_4491_, v_msg_4477_);
v___x_4493_ = l_Lean_Syntax_node2(v___x_4483_, v___x_4485_, v___x_4490_, v___x_4492_);
v___x_4494_ = l_Lean_Syntax_node1(v___x_4483_, v___x_4484_, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
lean_ctor_set(v___x_4495_, 1, v___y_4481_);
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4536_, v_a_4537_, v_a_4538_);
lean_dec_ref(v_a_4537_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_){
_start:
{
lean_object* v___x_4561_; uint8_t v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4558_);
v___x_4562_ = l_Lean_Syntax_isOfKind(v_x_4558_, v___x_4561_);
if (v___x_4562_ == 0)
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
lean_dec(v_x_4558_);
v___x_4563_ = lean_box(1);
v___x_4564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
lean_ctor_set(v___x_4564_, 1, v_a_4560_);
return v___x_4564_;
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v_a_4568_; lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
v___x_4565_ = lean_unsigned_to_nat(1u);
v___x_4566_ = l_Lean_Syntax_getArg(v_x_4558_, v___x_4565_);
lean_dec(v_x_4558_);
v___x_4567_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4566_, v_a_4559_, v_a_4560_);
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_a_4569_ = lean_ctor_get(v___x_4567_, 1);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4567_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4568_);
lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4577_, v_a_4578_, v_a_4579_);
lean_dec_ref(v_a_4578_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4581_){
_start:
{
lean_object* v___x_4583_; lean_object* v_issues_4584_; lean_object* v___x_4585_; 
v___x_4583_ = lean_st_ref_get(v_a_4581_);
v_issues_4584_ = lean_ctor_get(v___x_4583_, 10);
lean_inc(v_issues_4584_);
lean_dec(v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v_issues_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4586_);
lean_dec(v_a_4586_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v___x_4596_; 
v___x_4596_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4590_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_Lean_Meta_Sym_getIssues(v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4605_, lean_object* v_issues_4606_, lean_object* v_a_x3f_4607_){
_start:
{
lean_object* v___x_4609_; lean_object* v_share_4610_; lean_object* v_maxFVar_4611_; lean_object* v_proofInstInfo_4612_; lean_object* v_proofInstInfoFVar_4613_; lean_object* v_letValue_4614_; lean_object* v_inferType_4615_; lean_object* v_getLevel_4616_; lean_object* v_congrInfo_4617_; lean_object* v_defEqI_4618_; lean_object* v_extensions_4619_; lean_object* v_issues_4620_; lean_object* v_canon_4621_; lean_object* v_instanceOverrides_4622_; uint8_t v_debug_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4634_; 
v___x_4609_ = lean_st_ref_take(v_a_4605_);
v_share_4610_ = lean_ctor_get(v___x_4609_, 0);
v_maxFVar_4611_ = lean_ctor_get(v___x_4609_, 1);
v_proofInstInfo_4612_ = lean_ctor_get(v___x_4609_, 2);
v_proofInstInfoFVar_4613_ = lean_ctor_get(v___x_4609_, 3);
v_letValue_4614_ = lean_ctor_get(v___x_4609_, 4);
v_inferType_4615_ = lean_ctor_get(v___x_4609_, 5);
v_getLevel_4616_ = lean_ctor_get(v___x_4609_, 6);
v_congrInfo_4617_ = lean_ctor_get(v___x_4609_, 7);
v_defEqI_4618_ = lean_ctor_get(v___x_4609_, 8);
v_extensions_4619_ = lean_ctor_get(v___x_4609_, 9);
v_issues_4620_ = lean_ctor_get(v___x_4609_, 10);
v_canon_4621_ = lean_ctor_get(v___x_4609_, 11);
v_instanceOverrides_4622_ = lean_ctor_get(v___x_4609_, 12);
v_debug_4623_ = lean_ctor_get_uint8(v___x_4609_, sizeof(void*)*13);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4625_ = v___x_4609_;
v_isShared_4626_ = v_isSharedCheck_4634_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_instanceOverrides_4622_);
lean_inc(v_canon_4621_);
lean_inc(v_issues_4620_);
lean_inc(v_extensions_4619_);
lean_inc(v_defEqI_4618_);
lean_inc(v_congrInfo_4617_);
lean_inc(v_getLevel_4616_);
lean_inc(v_inferType_4615_);
lean_inc(v_letValue_4614_);
lean_inc(v_proofInstInfoFVar_4613_);
lean_inc(v_proofInstInfo_4612_);
lean_inc(v_maxFVar_4611_);
lean_inc(v_share_4610_);
lean_dec(v___x_4609_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4634_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4627_ = lean_box(0);
v___x_4628_ = l_List_appendTR___redArg(v_issues_4620_, v_issues_4606_);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 10, v___x_4628_);
v___x_4630_ = v___x_4625_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_share_4610_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v_maxFVar_4611_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_proofInstInfo_4612_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v_proofInstInfoFVar_4613_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_letValue_4614_);
lean_ctor_set(v_reuseFailAlloc_4633_, 5, v_inferType_4615_);
lean_ctor_set(v_reuseFailAlloc_4633_, 6, v_getLevel_4616_);
lean_ctor_set(v_reuseFailAlloc_4633_, 7, v_congrInfo_4617_);
lean_ctor_set(v_reuseFailAlloc_4633_, 8, v_defEqI_4618_);
lean_ctor_set(v_reuseFailAlloc_4633_, 9, v_extensions_4619_);
lean_ctor_set(v_reuseFailAlloc_4633_, 10, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4633_, 11, v_canon_4621_);
lean_ctor_set(v_reuseFailAlloc_4633_, 12, v_instanceOverrides_4622_);
lean_ctor_set_uint8(v_reuseFailAlloc_4633_, sizeof(void*)*13, v_debug_4623_);
v___x_4630_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = lean_st_ref_put(v_a_4605_, v___x_4630_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4627_);
return v___x_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4635_, lean_object* v_issues_4636_, lean_object* v_a_x3f_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4635_, v_issues_4636_, v_a_x3f_4637_);
lean_dec(v_a_x3f_4637_);
lean_dec(v_a_4635_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v___x_4648_; lean_object* v_issues_4649_; lean_object* v___x_4650_; lean_object* v_share_4651_; lean_object* v_maxFVar_4652_; lean_object* v_proofInstInfo_4653_; lean_object* v_proofInstInfoFVar_4654_; lean_object* v_letValue_4655_; lean_object* v_inferType_4656_; lean_object* v_getLevel_4657_; lean_object* v_congrInfo_4658_; lean_object* v_defEqI_4659_; lean_object* v_extensions_4660_; lean_object* v_canon_4661_; lean_object* v_instanceOverrides_4662_; uint8_t v_debug_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4701_; 
v___x_4648_ = lean_st_ref_get(v_a_4642_);
v_issues_4649_ = lean_ctor_get(v___x_4648_, 10);
lean_inc(v_issues_4649_);
lean_dec(v___x_4648_);
v___x_4650_ = lean_st_ref_take(v_a_4642_);
v_share_4651_ = lean_ctor_get(v___x_4650_, 0);
v_maxFVar_4652_ = lean_ctor_get(v___x_4650_, 1);
v_proofInstInfo_4653_ = lean_ctor_get(v___x_4650_, 2);
v_proofInstInfoFVar_4654_ = lean_ctor_get(v___x_4650_, 3);
v_letValue_4655_ = lean_ctor_get(v___x_4650_, 4);
v_inferType_4656_ = lean_ctor_get(v___x_4650_, 5);
v_getLevel_4657_ = lean_ctor_get(v___x_4650_, 6);
v_congrInfo_4658_ = lean_ctor_get(v___x_4650_, 7);
v_defEqI_4659_ = lean_ctor_get(v___x_4650_, 8);
v_extensions_4660_ = lean_ctor_get(v___x_4650_, 9);
v_canon_4661_ = lean_ctor_get(v___x_4650_, 11);
v_instanceOverrides_4662_ = lean_ctor_get(v___x_4650_, 12);
v_debug_4663_ = lean_ctor_get_uint8(v___x_4650_, sizeof(void*)*13);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4701_ == 0)
{
lean_object* v_unused_4702_; 
v_unused_4702_ = lean_ctor_get(v___x_4650_, 10);
lean_dec(v_unused_4702_);
v___x_4665_ = v___x_4650_;
v_isShared_4666_ = v_isSharedCheck_4701_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_instanceOverrides_4662_);
lean_inc(v_canon_4661_);
lean_inc(v_extensions_4660_);
lean_inc(v_defEqI_4659_);
lean_inc(v_congrInfo_4658_);
lean_inc(v_getLevel_4657_);
lean_inc(v_inferType_4656_);
lean_inc(v_letValue_4655_);
lean_inc(v_proofInstInfoFVar_4654_);
lean_inc(v_proofInstInfo_4653_);
lean_inc(v_maxFVar_4652_);
lean_inc(v_share_4651_);
lean_dec(v___x_4650_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4701_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4667_; lean_object* v___x_4669_; 
v___x_4667_ = lean_box(0);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 10, v___x_4667_);
v___x_4669_ = v___x_4665_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_share_4651_);
lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_maxFVar_4652_);
lean_ctor_set(v_reuseFailAlloc_4700_, 2, v_proofInstInfo_4653_);
lean_ctor_set(v_reuseFailAlloc_4700_, 3, v_proofInstInfoFVar_4654_);
lean_ctor_set(v_reuseFailAlloc_4700_, 4, v_letValue_4655_);
lean_ctor_set(v_reuseFailAlloc_4700_, 5, v_inferType_4656_);
lean_ctor_set(v_reuseFailAlloc_4700_, 6, v_getLevel_4657_);
lean_ctor_set(v_reuseFailAlloc_4700_, 7, v_congrInfo_4658_);
lean_ctor_set(v_reuseFailAlloc_4700_, 8, v_defEqI_4659_);
lean_ctor_set(v_reuseFailAlloc_4700_, 9, v_extensions_4660_);
lean_ctor_set(v_reuseFailAlloc_4700_, 10, v___x_4667_);
lean_ctor_set(v_reuseFailAlloc_4700_, 11, v_canon_4661_);
lean_ctor_set(v_reuseFailAlloc_4700_, 12, v_instanceOverrides_4662_);
lean_ctor_set_uint8(v_reuseFailAlloc_4700_, sizeof(void*)*13, v_debug_4663_);
v___x_4669_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
lean_object* v___x_4670_; lean_object* v_r_4671_; 
v___x_4670_ = lean_st_ref_put(v_a_4642_, v___x_4669_);
lean_inc(v_a_4646_);
lean_inc_ref(v_a_4645_);
lean_inc(v_a_4644_);
lean_inc_ref(v_a_4643_);
lean_inc(v_a_4642_);
lean_inc_ref(v_a_4641_);
v_r_4671_ = lean_apply_7(v_x_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, lean_box(0));
if (lean_obj_tag(v_r_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4688_; 
v_a_4672_ = lean_ctor_get(v_r_4671_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_r_4671_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4674_ = v_r_4671_;
v_isShared_4675_ = v_isSharedCheck_4688_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v_r_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4688_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
lean_inc(v_a_4672_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set_tag(v___x_4674_, 1);
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v___x_4678_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4642_, v_issues_4649_, v___x_4677_);
lean_dec_ref(v___x_4677_);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4685_ == 0)
{
lean_object* v_unused_4686_; 
v_unused_4686_ = lean_ctor_get(v___x_4678_, 0);
lean_dec(v_unused_4686_);
v___x_4680_ = v___x_4678_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_dec(v___x_4678_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
lean_ctor_set(v___x_4680_, 0, v_a_4672_);
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4672_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
v_a_4689_ = lean_ctor_get(v_r_4671_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v_r_4671_, 1);
v___x_4690_ = lean_box(0);
v___x_4691_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4642_, v_issues_4649_, v___x_4690_);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; 
v_unused_4699_ = lean_ctor_get(v___x_4691_, 0);
lean_dec(v_unused_4699_);
v___x_4693_ = v___x_4691_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_dec(v___x_4691_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
lean_ctor_set_tag(v___x_4693_, 1);
lean_ctor_set(v___x_4693_, 0, v_a_4689_);
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4689_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_a_4707_);
lean_dec_ref(v_a_4706_);
lean_dec(v_a_4705_);
lean_dec_ref(v_a_4704_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4712_, lean_object* v_x_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4722_, lean_object* v_x_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4722_, v_x_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4732_, lean_object* v_vals_4733_, lean_object* v_i_4734_, lean_object* v_k_4735_){
_start:
{
lean_object* v___x_4740_; uint8_t v___x_4741_; 
v___x_4740_ = lean_array_get_size(v_keys_4732_);
v___x_4741_ = lean_nat_dec_lt(v_i_4734_, v___x_4740_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; 
lean_dec(v_i_4734_);
v___x_4742_ = lean_box(0);
return v___x_4742_;
}
else
{
lean_object* v_fst_4743_; lean_object* v_snd_4744_; lean_object* v_k_x27_4745_; lean_object* v_fst_4746_; lean_object* v_snd_4747_; size_t v___x_4748_; size_t v___x_4749_; uint8_t v___x_4750_; 
v_fst_4743_ = lean_ctor_get(v_k_4735_, 0);
v_snd_4744_ = lean_ctor_get(v_k_4735_, 1);
v_k_x27_4745_ = lean_array_fget_borrowed(v_keys_4732_, v_i_4734_);
v_fst_4746_ = lean_ctor_get(v_k_x27_4745_, 0);
v_snd_4747_ = lean_ctor_get(v_k_x27_4745_, 1);
v___x_4748_ = lean_ptr_addr(v_fst_4743_);
v___x_4749_ = lean_ptr_addr(v_fst_4746_);
v___x_4750_ = lean_usize_dec_eq(v___x_4748_, v___x_4749_);
if (v___x_4750_ == 0)
{
goto v___jp_4736_;
}
else
{
size_t v___x_4751_; size_t v___x_4752_; uint8_t v___x_4753_; 
v___x_4751_ = lean_ptr_addr(v_snd_4744_);
v___x_4752_ = lean_ptr_addr(v_snd_4747_);
v___x_4753_ = lean_usize_dec_eq(v___x_4751_, v___x_4752_);
if (v___x_4753_ == 0)
{
goto v___jp_4736_;
}
else
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = lean_array_fget_borrowed(v_vals_4733_, v_i_4734_);
lean_dec(v_i_4734_);
lean_inc(v___x_4754_);
v___x_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
return v___x_4755_;
}
}
}
v___jp_4736_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = lean_unsigned_to_nat(1u);
v___x_4738_ = lean_nat_add(v_i_4734_, v___x_4737_);
lean_dec(v_i_4734_);
v_i_4734_ = v___x_4738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4756_, lean_object* v_vals_4757_, lean_object* v_i_4758_, lean_object* v_k_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4756_, v_vals_4757_, v_i_4758_, v_k_4759_);
lean_dec_ref(v_k_4759_);
lean_dec_ref(v_vals_4757_);
lean_dec_ref(v_keys_4756_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4761_, size_t v_x_4762_, lean_object* v_x_4763_){
_start:
{
if (lean_obj_tag(v_x_4761_) == 0)
{
lean_object* v_es_4764_; lean_object* v___x_4765_; size_t v___x_4766_; size_t v___x_4767_; lean_object* v_j_4768_; lean_object* v___x_4769_; 
v_es_4764_ = lean_ctor_get(v_x_4761_, 0);
v___x_4765_ = lean_box(2);
v___x_4766_ = ((size_t)31ULL);
v___x_4767_ = lean_usize_land(v_x_4762_, v___x_4766_);
v_j_4768_ = lean_usize_to_nat(v___x_4767_);
v___x_4769_ = lean_array_get_borrowed(v___x_4765_, v_es_4764_, v_j_4768_);
lean_dec(v_j_4768_);
switch(lean_obj_tag(v___x_4769_))
{
case 0:
{
lean_object* v_key_4770_; lean_object* v_val_4771_; lean_object* v_fst_4772_; lean_object* v_snd_4773_; lean_object* v_fst_4774_; lean_object* v_snd_4775_; size_t v___x_4776_; size_t v___x_4777_; uint8_t v___x_4778_; 
v_key_4770_ = lean_ctor_get(v___x_4769_, 0);
v_val_4771_ = lean_ctor_get(v___x_4769_, 1);
v_fst_4772_ = lean_ctor_get(v_x_4763_, 0);
v_snd_4773_ = lean_ctor_get(v_x_4763_, 1);
v_fst_4774_ = lean_ctor_get(v_key_4770_, 0);
v_snd_4775_ = lean_ctor_get(v_key_4770_, 1);
v___x_4776_ = lean_ptr_addr(v_fst_4772_);
v___x_4777_ = lean_ptr_addr(v_fst_4774_);
v___x_4778_ = lean_usize_dec_eq(v___x_4776_, v___x_4777_);
if (v___x_4778_ == 0)
{
lean_object* v___x_4779_; 
v___x_4779_ = lean_box(0);
return v___x_4779_;
}
else
{
size_t v___x_4780_; size_t v___x_4781_; uint8_t v___x_4782_; 
v___x_4780_ = lean_ptr_addr(v_snd_4773_);
v___x_4781_ = lean_ptr_addr(v_snd_4775_);
v___x_4782_ = lean_usize_dec_eq(v___x_4780_, v___x_4781_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_box(0);
return v___x_4783_;
}
else
{
lean_object* v___x_4784_; 
lean_inc(v_val_4771_);
v___x_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4784_, 0, v_val_4771_);
return v___x_4784_;
}
}
}
case 1:
{
lean_object* v_node_4785_; size_t v___x_4786_; size_t v___x_4787_; 
v_node_4785_ = lean_ctor_get(v___x_4769_, 0);
v___x_4786_ = ((size_t)5ULL);
v___x_4787_ = lean_usize_shift_right(v_x_4762_, v___x_4786_);
v_x_4761_ = v_node_4785_;
v_x_4762_ = v___x_4787_;
goto _start;
}
default: 
{
lean_object* v___x_4789_; 
v___x_4789_ = lean_box(0);
return v___x_4789_;
}
}
}
else
{
lean_object* v_ks_4790_; lean_object* v_vs_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v_ks_4790_ = lean_ctor_get(v_x_4761_, 0);
v_vs_4791_ = lean_ctor_get(v_x_4761_, 1);
v___x_4792_ = lean_unsigned_to_nat(0u);
v___x_4793_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4790_, v_vs_4791_, v___x_4792_, v_x_4763_);
return v___x_4793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4794_, lean_object* v_x_4795_, lean_object* v_x_4796_){
_start:
{
size_t v_x_2905__boxed_4797_; lean_object* v_res_4798_; 
v_x_2905__boxed_4797_ = lean_unbox_usize(v_x_4795_);
lean_dec(v_x_4795_);
v_res_4798_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4794_, v_x_2905__boxed_4797_, v_x_4796_);
lean_dec_ref(v_x_4796_);
lean_dec_ref(v_x_4794_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4799_, lean_object* v_x_4800_){
_start:
{
lean_object* v_fst_4801_; lean_object* v_snd_4802_; size_t v___x_4803_; size_t v___x_4804_; size_t v___x_4805_; uint64_t v___x_4806_; size_t v___x_4807_; size_t v___x_4808_; uint64_t v___x_4809_; uint64_t v___x_4810_; size_t v___x_4811_; lean_object* v___x_4812_; 
v_fst_4801_ = lean_ctor_get(v_x_4800_, 0);
v_snd_4802_ = lean_ctor_get(v_x_4800_, 1);
v___x_4803_ = lean_ptr_addr(v_fst_4801_);
v___x_4804_ = ((size_t)3ULL);
v___x_4805_ = lean_usize_shift_right(v___x_4803_, v___x_4804_);
v___x_4806_ = lean_usize_to_uint64(v___x_4805_);
v___x_4807_ = lean_ptr_addr(v_snd_4802_);
v___x_4808_ = lean_usize_shift_right(v___x_4807_, v___x_4804_);
v___x_4809_ = lean_usize_to_uint64(v___x_4808_);
v___x_4810_ = lean_uint64_mix_hash(v___x_4806_, v___x_4809_);
v___x_4811_ = lean_uint64_to_usize(v___x_4810_);
v___x_4812_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4799_, v___x_4811_, v_x_4800_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4813_, lean_object* v_x_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4813_, v_x_4814_);
lean_dec_ref(v_x_4814_);
lean_dec_ref(v_x_4813_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4816_, lean_object* v_x_4817_, lean_object* v_x_4818_, lean_object* v_x_4819_){
_start:
{
lean_object* v_ks_4820_; lean_object* v_vs_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4857_; 
v_ks_4820_ = lean_ctor_get(v_x_4816_, 0);
v_vs_4821_ = lean_ctor_get(v_x_4816_, 1);
v_isSharedCheck_4857_ = !lean_is_exclusive(v_x_4816_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4823_ = v_x_4816_;
v_isShared_4824_ = v_isSharedCheck_4857_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_vs_4821_);
lean_inc(v_ks_4820_);
lean_dec(v_x_4816_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4857_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4832_ = lean_array_get_size(v_ks_4820_);
v___x_4833_ = lean_nat_dec_lt(v_x_4817_, v___x_4832_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
lean_del_object(v___x_4823_);
lean_dec(v_x_4817_);
v___x_4834_ = lean_array_push(v_ks_4820_, v_x_4818_);
v___x_4835_ = lean_array_push(v_vs_4821_, v_x_4819_);
v___x_4836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
return v___x_4836_;
}
else
{
lean_object* v_fst_4837_; lean_object* v_snd_4838_; lean_object* v_k_x27_4839_; lean_object* v_fst_4840_; lean_object* v_snd_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4856_; 
v_fst_4837_ = lean_ctor_get(v_x_4818_, 0);
v_snd_4838_ = lean_ctor_get(v_x_4818_, 1);
v_k_x27_4839_ = lean_array_fget(v_ks_4820_, v_x_4817_);
v_fst_4840_ = lean_ctor_get(v_k_x27_4839_, 0);
v_snd_4841_ = lean_ctor_get(v_k_x27_4839_, 1);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_k_x27_4839_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4843_ = v_k_x27_4839_;
v_isShared_4844_ = v_isSharedCheck_4856_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_snd_4841_);
lean_inc(v_fst_4840_);
lean_dec(v_k_x27_4839_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4856_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
size_t v___x_4845_; size_t v___x_4846_; uint8_t v___x_4847_; 
v___x_4845_ = lean_ptr_addr(v_fst_4837_);
v___x_4846_ = lean_ptr_addr(v_fst_4840_);
lean_dec(v_fst_4840_);
v___x_4847_ = lean_usize_dec_eq(v___x_4845_, v___x_4846_);
if (v___x_4847_ == 0)
{
lean_del_object(v___x_4843_);
lean_dec(v_snd_4841_);
goto v___jp_4825_;
}
else
{
size_t v___x_4848_; size_t v___x_4849_; uint8_t v___x_4850_; 
v___x_4848_ = lean_ptr_addr(v_snd_4838_);
v___x_4849_ = lean_ptr_addr(v_snd_4841_);
lean_dec(v_snd_4841_);
v___x_4850_ = lean_usize_dec_eq(v___x_4848_, v___x_4849_);
if (v___x_4850_ == 0)
{
lean_del_object(v___x_4843_);
goto v___jp_4825_;
}
else
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4854_; 
lean_del_object(v___x_4823_);
v___x_4851_ = lean_array_fset(v_ks_4820_, v_x_4817_, v_x_4818_);
v___x_4852_ = lean_array_fset(v_vs_4821_, v_x_4817_, v_x_4819_);
lean_dec(v_x_4817_);
if (v_isShared_4844_ == 0)
{
lean_ctor_set_tag(v___x_4843_, 1);
lean_ctor_set(v___x_4843_, 1, v___x_4852_);
lean_ctor_set(v___x_4843_, 0, v___x_4851_);
v___x_4854_ = v___x_4843_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4855_, 1, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
v___jp_4825_:
{
lean_object* v___x_4827_; 
if (v_isShared_4824_ == 0)
{
v___x_4827_ = v___x_4823_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_ks_4820_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_vs_4821_);
v___x_4827_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = lean_unsigned_to_nat(1u);
v___x_4829_ = lean_nat_add(v_x_4817_, v___x_4828_);
lean_dec(v_x_4817_);
v_x_4816_ = v___x_4827_;
v_x_4817_ = v___x_4829_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4858_, lean_object* v_k_4859_, lean_object* v_v_4860_){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4861_ = lean_unsigned_to_nat(0u);
v___x_4862_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4858_, v___x_4861_, v_k_4859_, v_v_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4863_, size_t v_x_4864_, size_t v_x_4865_, lean_object* v_x_4866_, lean_object* v_x_4867_){
_start:
{
if (lean_obj_tag(v_x_4863_) == 0)
{
lean_object* v_es_4868_; size_t v___x_4869_; size_t v___x_4870_; lean_object* v_j_4871_; lean_object* v___x_4872_; uint8_t v___x_4873_; 
v_es_4868_ = lean_ctor_get(v_x_4863_, 0);
v___x_4869_ = ((size_t)31ULL);
v___x_4870_ = lean_usize_land(v_x_4864_, v___x_4869_);
v_j_4871_ = lean_usize_to_nat(v___x_4870_);
v___x_4872_ = lean_array_get_size(v_es_4868_);
v___x_4873_ = lean_nat_dec_lt(v_j_4871_, v___x_4872_);
if (v___x_4873_ == 0)
{
lean_dec(v_j_4871_);
lean_dec(v_x_4867_);
lean_dec_ref(v_x_4866_);
return v_x_4863_;
}
else
{
lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4922_; 
lean_inc_ref(v_es_4868_);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_x_4863_);
if (v_isSharedCheck_4922_ == 0)
{
lean_object* v_unused_4923_; 
v_unused_4923_ = lean_ctor_get(v_x_4863_, 0);
lean_dec(v_unused_4923_);
v___x_4875_ = v_x_4863_;
v_isShared_4876_ = v_isSharedCheck_4922_;
goto v_resetjp_4874_;
}
else
{
lean_dec(v_x_4863_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4922_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v_v_4877_; lean_object* v___x_4878_; lean_object* v_xs_x27_4879_; lean_object* v___y_4881_; 
v_v_4877_ = lean_array_fget(v_es_4868_, v_j_4871_);
v___x_4878_ = lean_box(0);
v_xs_x27_4879_ = lean_array_fset(v_es_4868_, v_j_4871_, v___x_4878_);
switch(lean_obj_tag(v_v_4877_))
{
case 0:
{
lean_object* v_key_4886_; lean_object* v_val_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4907_; 
v_key_4886_ = lean_ctor_get(v_v_4877_, 0);
v_val_4887_ = lean_ctor_get(v_v_4877_, 1);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_v_4877_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4889_ = v_v_4877_;
v_isShared_4890_ = v_isSharedCheck_4907_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_val_4887_);
lean_inc(v_key_4886_);
lean_dec(v_v_4877_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4907_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v_fst_4894_; lean_object* v_snd_4895_; lean_object* v_fst_4896_; lean_object* v_snd_4897_; size_t v___x_4898_; size_t v___x_4899_; uint8_t v___x_4900_; 
v_fst_4894_ = lean_ctor_get(v_x_4866_, 0);
v_snd_4895_ = lean_ctor_get(v_x_4866_, 1);
v_fst_4896_ = lean_ctor_get(v_key_4886_, 0);
v_snd_4897_ = lean_ctor_get(v_key_4886_, 1);
v___x_4898_ = lean_ptr_addr(v_fst_4894_);
v___x_4899_ = lean_ptr_addr(v_fst_4896_);
v___x_4900_ = lean_usize_dec_eq(v___x_4898_, v___x_4899_);
if (v___x_4900_ == 0)
{
lean_del_object(v___x_4889_);
goto v___jp_4891_;
}
else
{
size_t v___x_4901_; size_t v___x_4902_; uint8_t v___x_4903_; 
v___x_4901_ = lean_ptr_addr(v_snd_4895_);
v___x_4902_ = lean_ptr_addr(v_snd_4897_);
v___x_4903_ = lean_usize_dec_eq(v___x_4901_, v___x_4902_);
if (v___x_4903_ == 0)
{
lean_del_object(v___x_4889_);
goto v___jp_4891_;
}
else
{
lean_object* v___x_4905_; 
lean_dec(v_val_4887_);
lean_dec(v_key_4886_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 1, v_x_4867_);
lean_ctor_set(v___x_4889_, 0, v_x_4866_);
v___x_4905_ = v___x_4889_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_x_4866_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v_x_4867_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
v___y_4881_ = v___x_4905_;
goto v___jp_4880_;
}
}
}
v___jp_4891_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4886_, v_val_4887_, v_x_4866_, v_x_4867_);
v___x_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
v___y_4881_ = v___x_4893_;
goto v___jp_4880_;
}
}
}
case 1:
{
lean_object* v_node_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4920_; 
v_node_4908_ = lean_ctor_get(v_v_4877_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v_v_4877_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4910_ = v_v_4877_;
v_isShared_4911_ = v_isSharedCheck_4920_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_node_4908_);
lean_dec(v_v_4877_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4920_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
size_t v___x_4912_; size_t v___x_4913_; size_t v___x_4914_; size_t v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4912_ = ((size_t)5ULL);
v___x_4913_ = lean_usize_shift_right(v_x_4864_, v___x_4912_);
v___x_4914_ = ((size_t)1ULL);
v___x_4915_ = lean_usize_add(v_x_4865_, v___x_4914_);
v___x_4916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4908_, v___x_4913_, v___x_4915_, v_x_4866_, v_x_4867_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 0, v___x_4916_);
v___x_4918_ = v___x_4910_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
v___y_4881_ = v___x_4918_;
goto v___jp_4880_;
}
}
}
default: 
{
lean_object* v___x_4921_; 
v___x_4921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4921_, 0, v_x_4866_);
lean_ctor_set(v___x_4921_, 1, v_x_4867_);
v___y_4881_ = v___x_4921_;
goto v___jp_4880_;
}
}
v___jp_4880_:
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4882_ = lean_array_fset(v_xs_x27_4879_, v_j_4871_, v___y_4881_);
lean_dec(v_j_4871_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 0, v___x_4882_);
v___x_4884_ = v___x_4875_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
else
{
lean_object* v_ks_4924_; lean_object* v_vs_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4943_; 
v_ks_4924_ = lean_ctor_get(v_x_4863_, 0);
v_vs_4925_ = lean_ctor_get(v_x_4863_, 1);
v_isSharedCheck_4943_ = !lean_is_exclusive(v_x_4863_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4927_ = v_x_4863_;
v_isShared_4928_ = v_isSharedCheck_4943_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_vs_4925_);
lean_inc(v_ks_4924_);
lean_dec(v_x_4863_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4943_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_ks_4924_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_vs_4925_);
v___x_4930_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v_newNode_4931_; size_t v___x_4932_; uint8_t v___x_4933_; 
v_newNode_4931_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4930_, v_x_4866_, v_x_4867_);
v___x_4932_ = ((size_t)7ULL);
v___x_4933_ = lean_usize_dec_le(v___x_4932_, v_x_4865_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; uint8_t v___x_4936_; 
v___x_4934_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4931_);
v___x_4935_ = lean_unsigned_to_nat(4u);
v___x_4936_ = lean_nat_dec_lt(v___x_4934_, v___x_4935_);
lean_dec(v___x_4934_);
if (v___x_4936_ == 0)
{
lean_object* v_ks_4937_; lean_object* v_vs_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v_ks_4937_ = lean_ctor_get(v_newNode_4931_, 0);
lean_inc_ref(v_ks_4937_);
v_vs_4938_ = lean_ctor_get(v_newNode_4931_, 1);
lean_inc_ref(v_vs_4938_);
lean_dec_ref(v_newNode_4931_);
v___x_4939_ = lean_unsigned_to_nat(0u);
v___x_4940_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getLetValueS_x3f_spec__1_spec__2___redArg___closed__0);
v___x_4941_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4865_, v_ks_4937_, v_vs_4938_, v___x_4939_, v___x_4940_);
lean_dec_ref(v_vs_4938_);
lean_dec_ref(v_ks_4937_);
return v___x_4941_;
}
else
{
return v_newNode_4931_;
}
}
else
{
return v_newNode_4931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4944_, lean_object* v_keys_4945_, lean_object* v_vals_4946_, lean_object* v_i_4947_, lean_object* v_entries_4948_){
_start:
{
lean_object* v___x_4949_; uint8_t v___x_4950_; 
v___x_4949_ = lean_array_get_size(v_keys_4945_);
v___x_4950_ = lean_nat_dec_lt(v_i_4947_, v___x_4949_);
if (v___x_4950_ == 0)
{
lean_dec(v_i_4947_);
return v_entries_4948_;
}
else
{
lean_object* v_k_4951_; lean_object* v_fst_4952_; lean_object* v_snd_4953_; lean_object* v_v_4954_; size_t v___x_4955_; size_t v___x_4956_; size_t v___x_4957_; uint64_t v___x_4958_; size_t v___x_4959_; size_t v___x_4960_; uint64_t v___x_4961_; uint64_t v___x_4962_; size_t v_h_4963_; size_t v___x_4964_; lean_object* v___x_4965_; size_t v___x_4966_; size_t v___x_4967_; size_t v___x_4968_; size_t v_h_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_k_4951_ = lean_array_fget_borrowed(v_keys_4945_, v_i_4947_);
v_fst_4952_ = lean_ctor_get(v_k_4951_, 0);
v_snd_4953_ = lean_ctor_get(v_k_4951_, 1);
v_v_4954_ = lean_array_fget_borrowed(v_vals_4946_, v_i_4947_);
v___x_4955_ = lean_ptr_addr(v_fst_4952_);
v___x_4956_ = ((size_t)3ULL);
v___x_4957_ = lean_usize_shift_right(v___x_4955_, v___x_4956_);
v___x_4958_ = lean_usize_to_uint64(v___x_4957_);
v___x_4959_ = lean_ptr_addr(v_snd_4953_);
v___x_4960_ = lean_usize_shift_right(v___x_4959_, v___x_4956_);
v___x_4961_ = lean_usize_to_uint64(v___x_4960_);
v___x_4962_ = lean_uint64_mix_hash(v___x_4958_, v___x_4961_);
v_h_4963_ = lean_uint64_to_usize(v___x_4962_);
v___x_4964_ = ((size_t)5ULL);
v___x_4965_ = lean_unsigned_to_nat(1u);
v___x_4966_ = ((size_t)1ULL);
v___x_4967_ = lean_usize_sub(v_depth_4944_, v___x_4966_);
v___x_4968_ = lean_usize_mul(v___x_4964_, v___x_4967_);
v_h_4969_ = lean_usize_shift_right(v_h_4963_, v___x_4968_);
v___x_4970_ = lean_nat_add(v_i_4947_, v___x_4965_);
lean_dec(v_i_4947_);
lean_inc(v_v_4954_);
lean_inc(v_k_4951_);
v___x_4971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4948_, v_h_4969_, v_depth_4944_, v_k_4951_, v_v_4954_);
v_i_4947_ = v___x_4970_;
v_entries_4948_ = v___x_4971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4973_, lean_object* v_keys_4974_, lean_object* v_vals_4975_, lean_object* v_i_4976_, lean_object* v_entries_4977_){
_start:
{
size_t v_depth_boxed_4978_; lean_object* v_res_4979_; 
v_depth_boxed_4978_ = lean_unbox_usize(v_depth_4973_);
lean_dec(v_depth_4973_);
v_res_4979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4978_, v_keys_4974_, v_vals_4975_, v_i_4976_, v_entries_4977_);
lean_dec_ref(v_vals_4975_);
lean_dec_ref(v_keys_4974_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4980_, lean_object* v_x_4981_, lean_object* v_x_4982_, lean_object* v_x_4983_, lean_object* v_x_4984_){
_start:
{
size_t v_x_3110__boxed_4985_; size_t v_x_3111__boxed_4986_; lean_object* v_res_4987_; 
v_x_3110__boxed_4985_ = lean_unbox_usize(v_x_4981_);
lean_dec(v_x_4981_);
v_x_3111__boxed_4986_ = lean_unbox_usize(v_x_4982_);
lean_dec(v_x_4982_);
v_res_4987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4980_, v_x_3110__boxed_4985_, v_x_3111__boxed_4986_, v_x_4983_, v_x_4984_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4988_, lean_object* v_x_4989_, lean_object* v_x_4990_){
_start:
{
lean_object* v_fst_4991_; lean_object* v_snd_4992_; size_t v___x_4993_; size_t v___x_4994_; size_t v___x_4995_; uint64_t v___x_4996_; size_t v___x_4997_; size_t v___x_4998_; uint64_t v___x_4999_; uint64_t v___x_5000_; size_t v___x_5001_; size_t v___x_5002_; lean_object* v___x_5003_; 
v_fst_4991_ = lean_ctor_get(v_x_4989_, 0);
v_snd_4992_ = lean_ctor_get(v_x_4989_, 1);
v___x_4993_ = lean_ptr_addr(v_fst_4991_);
v___x_4994_ = ((size_t)3ULL);
v___x_4995_ = lean_usize_shift_right(v___x_4993_, v___x_4994_);
v___x_4996_ = lean_usize_to_uint64(v___x_4995_);
v___x_4997_ = lean_ptr_addr(v_snd_4992_);
v___x_4998_ = lean_usize_shift_right(v___x_4997_, v___x_4994_);
v___x_4999_ = lean_usize_to_uint64(v___x_4998_);
v___x_5000_ = lean_uint64_mix_hash(v___x_4996_, v___x_4999_);
v___x_5001_ = lean_uint64_to_usize(v___x_5000_);
v___x_5002_ = ((size_t)1ULL);
v___x_5003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4988_, v___x_5001_, v___x_5002_, v_x_4989_, v_x_4990_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_5004_, lean_object* v_t_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v_key_5012_; lean_object* v___x_5013_; lean_object* v_defEqI_5014_; lean_object* v___x_5015_; 
lean_inc_ref(v_t_5005_);
lean_inc_ref(v_s_5004_);
v_key_5012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_5012_, 0, v_s_5004_);
lean_ctor_set(v_key_5012_, 1, v_t_5005_);
v___x_5013_ = lean_st_ref_get(v_a_5006_);
v_defEqI_5014_ = lean_ctor_get(v___x_5013_, 8);
lean_inc_ref(v_defEqI_5014_);
lean_dec(v___x_5013_);
v___x_5015_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_5014_, v_key_5012_);
lean_dec_ref(v_defEqI_5014_);
if (lean_obj_tag(v___x_5015_) == 1)
{
lean_object* v_val_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
lean_dec_ref_known(v_key_5012_, 2);
lean_dec_ref(v_t_5005_);
lean_dec_ref(v_s_5004_);
v_val_5016_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5015_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_val_5016_);
lean_dec(v___x_5015_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set_tag(v___x_5018_, 0);
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_val_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
else
{
lean_object* v___x_5024_; 
lean_dec(v___x_5015_);
v___x_5024_ = l_Lean_Meta_isDefEqI(v_s_5004_, v_t_5005_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5056_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5027_ = v___x_5024_;
v_isShared_5028_ = v_isSharedCheck_5056_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5024_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5056_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5029_; lean_object* v_share_5030_; lean_object* v_maxFVar_5031_; lean_object* v_proofInstInfo_5032_; lean_object* v_proofInstInfoFVar_5033_; lean_object* v_letValue_5034_; lean_object* v_inferType_5035_; lean_object* v_getLevel_5036_; lean_object* v_congrInfo_5037_; lean_object* v_defEqI_5038_; lean_object* v_extensions_5039_; lean_object* v_issues_5040_; lean_object* v_canon_5041_; lean_object* v_instanceOverrides_5042_; uint8_t v_debug_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5055_; 
v___x_5029_ = lean_st_ref_take(v_a_5006_);
v_share_5030_ = lean_ctor_get(v___x_5029_, 0);
v_maxFVar_5031_ = lean_ctor_get(v___x_5029_, 1);
v_proofInstInfo_5032_ = lean_ctor_get(v___x_5029_, 2);
v_proofInstInfoFVar_5033_ = lean_ctor_get(v___x_5029_, 3);
v_letValue_5034_ = lean_ctor_get(v___x_5029_, 4);
v_inferType_5035_ = lean_ctor_get(v___x_5029_, 5);
v_getLevel_5036_ = lean_ctor_get(v___x_5029_, 6);
v_congrInfo_5037_ = lean_ctor_get(v___x_5029_, 7);
v_defEqI_5038_ = lean_ctor_get(v___x_5029_, 8);
v_extensions_5039_ = lean_ctor_get(v___x_5029_, 9);
v_issues_5040_ = lean_ctor_get(v___x_5029_, 10);
v_canon_5041_ = lean_ctor_get(v___x_5029_, 11);
v_instanceOverrides_5042_ = lean_ctor_get(v___x_5029_, 12);
v_debug_5043_ = lean_ctor_get_uint8(v___x_5029_, sizeof(void*)*13);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5045_ = v___x_5029_;
v_isShared_5046_ = v_isSharedCheck_5055_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_instanceOverrides_5042_);
lean_inc(v_canon_5041_);
lean_inc(v_issues_5040_);
lean_inc(v_extensions_5039_);
lean_inc(v_defEqI_5038_);
lean_inc(v_congrInfo_5037_);
lean_inc(v_getLevel_5036_);
lean_inc(v_inferType_5035_);
lean_inc(v_letValue_5034_);
lean_inc(v_proofInstInfoFVar_5033_);
lean_inc(v_proofInstInfo_5032_);
lean_inc(v_maxFVar_5031_);
lean_inc(v_share_5030_);
lean_dec(v___x_5029_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5055_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5047_; lean_object* v___x_5049_; 
lean_inc(v_a_5025_);
v___x_5047_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_5038_, v_key_5012_, v_a_5025_);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 8, v___x_5047_);
v___x_5049_ = v___x_5045_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_share_5030_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v_maxFVar_5031_);
lean_ctor_set(v_reuseFailAlloc_5054_, 2, v_proofInstInfo_5032_);
lean_ctor_set(v_reuseFailAlloc_5054_, 3, v_proofInstInfoFVar_5033_);
lean_ctor_set(v_reuseFailAlloc_5054_, 4, v_letValue_5034_);
lean_ctor_set(v_reuseFailAlloc_5054_, 5, v_inferType_5035_);
lean_ctor_set(v_reuseFailAlloc_5054_, 6, v_getLevel_5036_);
lean_ctor_set(v_reuseFailAlloc_5054_, 7, v_congrInfo_5037_);
lean_ctor_set(v_reuseFailAlloc_5054_, 8, v___x_5047_);
lean_ctor_set(v_reuseFailAlloc_5054_, 9, v_extensions_5039_);
lean_ctor_set(v_reuseFailAlloc_5054_, 10, v_issues_5040_);
lean_ctor_set(v_reuseFailAlloc_5054_, 11, v_canon_5041_);
lean_ctor_set(v_reuseFailAlloc_5054_, 12, v_instanceOverrides_5042_);
lean_ctor_set_uint8(v_reuseFailAlloc_5054_, sizeof(void*)*13, v_debug_5043_);
v___x_5049_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
lean_object* v___x_5050_; lean_object* v___x_5052_; 
v___x_5050_ = lean_st_ref_put(v_a_5006_, v___x_5049_);
if (v_isShared_5028_ == 0)
{
v___x_5052_ = v___x_5027_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5025_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_5012_, 2);
return v___x_5024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_5057_, lean_object* v_t_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_5057_, v_t_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_a_5059_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_5066_, lean_object* v_t_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_5066_, v_t_5067_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_5076_, lean_object* v_t_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Meta_Sym_isDefEqI(v_s_5076_, v_t_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_a_5078_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_5086_, lean_object* v_x_5087_, lean_object* v_x_5088_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_5087_, v_x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_5090_, lean_object* v_x_5091_, lean_object* v_x_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_5090_, v_x_5091_, v_x_5092_);
lean_dec_ref(v_x_5092_);
lean_dec_ref(v_x_5091_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_5094_, lean_object* v_x_5095_, lean_object* v_x_5096_, lean_object* v_x_5097_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_5095_, v_x_5096_, v_x_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_5099_, lean_object* v_x_5100_, size_t v_x_5101_, lean_object* v_x_5102_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_5100_, v_x_5101_, v_x_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5104_, lean_object* v_x_5105_, lean_object* v_x_5106_, lean_object* v_x_5107_){
_start:
{
size_t v_x_3405__boxed_5108_; lean_object* v_res_5109_; 
v_x_3405__boxed_5108_ = lean_unbox_usize(v_x_5106_);
lean_dec(v_x_5106_);
v_res_5109_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_5104_, v_x_5105_, v_x_3405__boxed_5108_, v_x_5107_);
lean_dec_ref(v_x_5107_);
lean_dec_ref(v_x_5105_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_5110_, lean_object* v_x_5111_, size_t v_x_5112_, size_t v_x_5113_, lean_object* v_x_5114_, lean_object* v_x_5115_){
_start:
{
lean_object* v___x_5116_; 
v___x_5116_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_5111_, v_x_5112_, v_x_5113_, v_x_5114_, v_x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5117_, lean_object* v_x_5118_, lean_object* v_x_5119_, lean_object* v_x_5120_, lean_object* v_x_5121_, lean_object* v_x_5122_){
_start:
{
size_t v_x_3416__boxed_5123_; size_t v_x_3417__boxed_5124_; lean_object* v_res_5125_; 
v_x_3416__boxed_5123_ = lean_unbox_usize(v_x_5119_);
lean_dec(v_x_5119_);
v_x_3417__boxed_5124_ = lean_unbox_usize(v_x_5120_);
lean_dec(v_x_5120_);
v_res_5125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_5117_, v_x_5118_, v_x_3416__boxed_5123_, v_x_3417__boxed_5124_, v_x_5121_, v_x_5122_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5126_, lean_object* v_keys_5127_, lean_object* v_vals_5128_, lean_object* v_heq_5129_, lean_object* v_i_5130_, lean_object* v_k_5131_){
_start:
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_5127_, v_vals_5128_, v_i_5130_, v_k_5131_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5133_, lean_object* v_keys_5134_, lean_object* v_vals_5135_, lean_object* v_heq_5136_, lean_object* v_i_5137_, lean_object* v_k_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_5133_, v_keys_5134_, v_vals_5135_, v_heq_5136_, v_i_5137_, v_k_5138_);
lean_dec_ref(v_k_5138_);
lean_dec_ref(v_vals_5135_);
lean_dec_ref(v_keys_5134_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_5140_, lean_object* v_n_5141_, lean_object* v_k_5142_, lean_object* v_v_5143_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_5141_, v_k_5142_, v_v_5143_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_5145_, size_t v_depth_5146_, lean_object* v_keys_5147_, lean_object* v_vals_5148_, lean_object* v_heq_5149_, lean_object* v_i_5150_, lean_object* v_entries_5151_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_5146_, v_keys_5147_, v_vals_5148_, v_i_5150_, v_entries_5151_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_5153_, lean_object* v_depth_5154_, lean_object* v_keys_5155_, lean_object* v_vals_5156_, lean_object* v_heq_5157_, lean_object* v_i_5158_, lean_object* v_entries_5159_){
_start:
{
size_t v_depth_boxed_5160_; lean_object* v_res_5161_; 
v_depth_boxed_5160_ = lean_unbox_usize(v_depth_5154_);
lean_dec(v_depth_5154_);
v_res_5161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_5153_, v_depth_boxed_5160_, v_keys_5155_, v_vals_5156_, v_heq_5157_, v_i_5158_, v_entries_5159_);
lean_dec_ref(v_vals_5156_);
lean_dec_ref(v_keys_5155_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_5162_, lean_object* v_x_5163_, lean_object* v_x_5164_, lean_object* v_x_5165_, lean_object* v_x_5166_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_5163_, v_x_5164_, v_x_5165_, v_x_5166_);
return v___x_5167_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0(void){
_start:
{
lean_object* v___x_5168_; lean_object* v___f_5169_; 
v___x_5168_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_5169_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5169_, 0, v___x_5168_);
return v___f_5169_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1(void){
_start:
{
lean_object* v___x_5170_; lean_object* v___f_5171_; 
v___x_5170_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_5171_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5171_, 0, v___x_5170_);
return v___f_5171_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2(void){
_start:
{
lean_object* v___f_5172_; lean_object* v___f_5173_; lean_object* v___x_5174_; 
v___f_5172_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1);
v___f_5173_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0);
v___x_5174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5174_, 0, v___f_5173_);
lean_ctor_set(v___x_5174_, 1, v___f_5172_);
return v___x_5174_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3(void){
_start:
{
lean_object* v___x_5175_; lean_object* v___f_5176_; 
v___x_5175_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_5176_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5176_, 0, v___x_5175_);
return v___f_5176_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4(void){
_start:
{
lean_object* v___x_5177_; lean_object* v___f_5178_; 
v___x_5177_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_5178_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5178_, 0, v___x_5177_);
return v___f_5178_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5(void){
_start:
{
lean_object* v___f_5179_; lean_object* v___f_5180_; lean_object* v___x_5181_; 
v___f_5179_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4);
v___f_5180_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3);
v___x_5181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___f_5180_);
lean_ctor_set(v___x_5181_, 1, v___f_5179_);
return v___x_5181_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6(void){
_start:
{
lean_object* v___x_5182_; lean_object* v___f_5183_; 
v___x_5182_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_5183_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5183_, 0, v___x_5182_);
return v___f_5183_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7(void){
_start:
{
lean_object* v___x_5184_; lean_object* v___f_5185_; 
v___x_5184_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_5185_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5185_, 0, v___x_5184_);
return v___f_5185_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8(void){
_start:
{
lean_object* v___f_5186_; lean_object* v___f_5187_; lean_object* v___x_5188_; 
v___f_5186_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7);
v___f_5187_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6);
v___x_5188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___f_5187_);
lean_ctor_set(v___x_5188_, 1, v___f_5186_);
return v___x_5188_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9(void){
_start:
{
lean_object* v___x_5189_; lean_object* v___f_5190_; 
v___x_5189_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_5190_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5190_, 0, v___x_5189_);
return v___f_5190_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10(void){
_start:
{
lean_object* v___x_5191_; lean_object* v___f_5192_; 
v___x_5191_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_5192_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_5192_, 0, v___x_5191_);
return v___f_5192_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11(void){
_start:
{
lean_object* v___f_5193_; lean_object* v___f_5194_; lean_object* v___x_5195_; 
v___f_5193_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10);
v___f_5194_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9);
v___x_5195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5195_, 0, v___f_5194_);
lean_ctor_set(v___x_5195_, 1, v___f_5193_);
return v___x_5195_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16(void){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; 
v___x_5200_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_5201_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5202_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_5203_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_5202_, v___x_5201_, v___x_5200_);
return v___x_5203_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17(void){
_start:
{
lean_object* v___x_5204_; lean_object* v___f_5205_; lean_object* v___f_5206_; lean_object* v___x_5207_; 
v___x_5204_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16);
v___f_5205_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5206_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_5207_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_5206_, v___f_5205_, v___x_5204_);
return v___x_5207_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18(void){
_start:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5208_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17);
v___x_5209_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5210_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_5211_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_5210_, v___x_5209_, v___x_5208_);
return v___x_5211_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19(void){
_start:
{
lean_object* v___x_5212_; lean_object* v___f_5213_; lean_object* v___f_5214_; lean_object* v___x_5215_; 
v___x_5212_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18);
v___f_5213_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5214_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_5215_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_5214_, v___f_5213_, v___x_5212_);
return v___x_5215_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20(void){
_start:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___f_5218_; 
v___x_5216_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_5217_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_5218_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5218_, 0, v___x_5217_);
lean_closure_set(v___f_5218_, 1, v___x_5216_);
return v___f_5218_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21(void){
_start:
{
lean_object* v___f_5219_; lean_object* v___f_5220_; lean_object* v___f_5221_; 
v___f_5219_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_5220_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20);
v___f_5221_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5221_, 0, v___f_5220_);
lean_closure_set(v___f_5221_, 1, v___f_5219_);
return v___f_5221_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23(void){
_start:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5223_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22));
v___x_5224_ = l_Lean_stringToMessageData(v___x_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg(){
_start:
{
lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v_toApplicative_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5295_; 
v___x_5226_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_5227_ = l_StateRefT_x27_instMonad___redArg(v___x_5226_);
v_toApplicative_5228_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5295_ == 0)
{
lean_object* v_unused_5296_; 
v_unused_5296_ = lean_ctor_get(v___x_5227_, 1);
lean_dec(v_unused_5296_);
v___x_5230_ = v___x_5227_;
v_isShared_5231_ = v_isSharedCheck_5295_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_toApplicative_5228_);
lean_dec(v___x_5227_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5295_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v_toFunctor_5232_; lean_object* v_toSeq_5233_; lean_object* v_toSeqLeft_5234_; lean_object* v_toSeqRight_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5293_; 
v_toFunctor_5232_ = lean_ctor_get(v_toApplicative_5228_, 0);
v_toSeq_5233_ = lean_ctor_get(v_toApplicative_5228_, 2);
v_toSeqLeft_5234_ = lean_ctor_get(v_toApplicative_5228_, 3);
v_toSeqRight_5235_ = lean_ctor_get(v_toApplicative_5228_, 4);
v_isSharedCheck_5293_ = !lean_is_exclusive(v_toApplicative_5228_);
if (v_isSharedCheck_5293_ == 0)
{
lean_object* v_unused_5294_; 
v_unused_5294_ = lean_ctor_get(v_toApplicative_5228_, 1);
lean_dec(v_unused_5294_);
v___x_5237_ = v_toApplicative_5228_;
v_isShared_5238_ = v_isSharedCheck_5293_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_toSeqRight_5235_);
lean_inc(v_toSeqLeft_5234_);
lean_inc(v_toSeq_5233_);
lean_inc(v_toFunctor_5232_);
lean_dec(v_toApplicative_5228_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5293_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___f_5239_; lean_object* v___f_5240_; lean_object* v___f_5241_; lean_object* v___f_5242_; lean_object* v___x_5243_; lean_object* v___f_5244_; lean_object* v___f_5245_; lean_object* v___f_5246_; lean_object* v___x_5248_; 
v___f_5239_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_5240_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_5232_);
v___f_5241_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5241_, 0, v_toFunctor_5232_);
v___f_5242_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5242_, 0, v_toFunctor_5232_);
v___x_5243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___f_5241_);
lean_ctor_set(v___x_5243_, 1, v___f_5242_);
v___f_5244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5244_, 0, v_toSeqRight_5235_);
v___f_5245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5245_, 0, v_toSeqLeft_5234_);
v___f_5246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5246_, 0, v_toSeq_5233_);
if (v_isShared_5238_ == 0)
{
lean_ctor_set(v___x_5237_, 4, v___f_5244_);
lean_ctor_set(v___x_5237_, 3, v___f_5245_);
lean_ctor_set(v___x_5237_, 2, v___f_5246_);
lean_ctor_set(v___x_5237_, 1, v___f_5239_);
lean_ctor_set(v___x_5237_, 0, v___x_5243_);
v___x_5248_ = v___x_5237_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5292_, 1, v___f_5239_);
lean_ctor_set(v_reuseFailAlloc_5292_, 2, v___f_5246_);
lean_ctor_set(v_reuseFailAlloc_5292_, 3, v___f_5245_);
lean_ctor_set(v_reuseFailAlloc_5292_, 4, v___f_5244_);
v___x_5248_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5250_; 
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 1, v___f_5240_);
lean_ctor_set(v___x_5230_, 0, v___x_5248_);
v___x_5250_ = v___x_5230_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v___x_5248_);
lean_ctor_set(v_reuseFailAlloc_5291_, 1, v___f_5240_);
v___x_5250_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
lean_object* v___x_5251_; lean_object* v_toApplicative_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5289_; 
v___x_5251_ = l_StateRefT_x27_instMonad___redArg(v___x_5250_);
v_toApplicative_5252_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5289_ == 0)
{
lean_object* v_unused_5290_; 
v_unused_5290_ = lean_ctor_get(v___x_5251_, 1);
lean_dec(v_unused_5290_);
v___x_5254_ = v___x_5251_;
v_isShared_5255_ = v_isSharedCheck_5289_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_toApplicative_5252_);
lean_dec(v___x_5251_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5289_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v_toFunctor_5256_; lean_object* v_toSeq_5257_; lean_object* v_toSeqLeft_5258_; lean_object* v_toSeqRight_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5287_; 
v_toFunctor_5256_ = lean_ctor_get(v_toApplicative_5252_, 0);
v_toSeq_5257_ = lean_ctor_get(v_toApplicative_5252_, 2);
v_toSeqLeft_5258_ = lean_ctor_get(v_toApplicative_5252_, 3);
v_toSeqRight_5259_ = lean_ctor_get(v_toApplicative_5252_, 4);
v_isSharedCheck_5287_ = !lean_is_exclusive(v_toApplicative_5252_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; 
v_unused_5288_ = lean_ctor_get(v_toApplicative_5252_, 1);
lean_dec(v_unused_5288_);
v___x_5261_ = v_toApplicative_5252_;
v_isShared_5262_ = v_isSharedCheck_5287_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_toSeqRight_5259_);
lean_inc(v_toSeqLeft_5258_);
lean_inc(v_toSeq_5257_);
lean_inc(v_toFunctor_5256_);
lean_dec(v_toApplicative_5252_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5287_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___f_5263_; lean_object* v___f_5264_; lean_object* v___f_5265_; lean_object* v___f_5266_; lean_object* v___x_5267_; lean_object* v___f_5268_; lean_object* v___f_5269_; lean_object* v___f_5270_; lean_object* v___x_5272_; 
v___f_5263_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_5264_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_5256_);
v___f_5265_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5265_, 0, v_toFunctor_5256_);
v___f_5266_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5266_, 0, v_toFunctor_5256_);
v___x_5267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5267_, 0, v___f_5265_);
lean_ctor_set(v___x_5267_, 1, v___f_5266_);
v___f_5268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5268_, 0, v_toSeqRight_5259_);
v___f_5269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5269_, 0, v_toSeqLeft_5258_);
v___f_5270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5270_, 0, v_toSeq_5257_);
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 4, v___f_5268_);
lean_ctor_set(v___x_5261_, 3, v___f_5269_);
lean_ctor_set(v___x_5261_, 2, v___f_5270_);
lean_ctor_set(v___x_5261_, 1, v___f_5263_);
lean_ctor_set(v___x_5261_, 0, v___x_5267_);
v___x_5272_ = v___x_5261_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5267_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v___f_5263_);
lean_ctor_set(v_reuseFailAlloc_5286_, 2, v___f_5270_);
lean_ctor_set(v_reuseFailAlloc_5286_, 3, v___f_5269_);
lean_ctor_set(v_reuseFailAlloc_5286_, 4, v___f_5268_);
v___x_5272_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5274_; 
if (v_isShared_5255_ == 0)
{
lean_ctor_set(v___x_5254_, 1, v___f_5264_);
lean_ctor_set(v___x_5254_, 0, v___x_5272_);
v___x_5274_ = v___x_5254_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5272_);
lean_ctor_set(v_reuseFailAlloc_5285_, 1, v___f_5264_);
v___x_5274_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v_toMonadRef_5279_; lean_object* v___f_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5275_ = l_StateRefT_x27_instMonad___redArg(v___x_5274_);
v___x_5276_ = l_ReaderT_instMonad___redArg(v___x_5275_);
v___x_5277_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11);
v___x_5278_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19);
v_toMonadRef_5279_ = lean_ctor_get(v___x_5278_, 0);
v___f_5280_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21);
lean_inc_ref(v___x_5276_);
v___x_5281_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_5280_, v___x_5276_);
lean_inc_ref(v_toMonadRef_5279_);
v___x_5282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5277_);
lean_ctor_set(v___x_5282_, 1, v_toMonadRef_5279_);
lean_ctor_set(v___x_5282_, 2, v___x_5281_);
v___x_5283_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23);
v___x_5284_ = l_Lean_throwError___redArg(v___x_5276_, v___x_5282_, v___x_5283_);
return v___x_5284_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object* v___dummy_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v_res_5298_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_5300_){
_start:
{
lean_object* v___x_5301_; 
v___x_5301_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_5302_, lean_object* v_extensions_5303_){
_start:
{
lean_object* v_id_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v_id_5305_ = lean_ctor_get(v_ext_5302_, 0);
v___x_5306_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_5307_ = lean_array_get_borrowed(v___x_5306_, v_extensions_5303_, v_id_5305_);
lean_inc(v___x_5307_);
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_5309_, lean_object* v_extensions_5310_, lean_object* v_a_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5309_, v_extensions_5310_);
lean_dec_ref(v_extensions_5310_);
lean_dec_ref(v_ext_5309_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_5313_, lean_object* v_ext_5314_, lean_object* v_extensions_5315_){
_start:
{
lean_object* v___x_5317_; 
v___x_5317_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5314_, v_extensions_5315_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_5318_, lean_object* v_ext_5319_, lean_object* v_extensions_5320_, lean_object* v_a_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_5318_, v_ext_5319_, v_extensions_5320_);
lean_dec_ref(v_extensions_5320_);
lean_dec_ref(v_ext_5319_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_){
_start:
{
lean_object* v___x_5327_; lean_object* v_extensions_5328_; lean_object* v_ref_5329_; lean_object* v___x_5330_; 
v___x_5327_ = lean_st_ref_get(v_a_5324_);
v_extensions_5328_ = lean_ctor_get(v___x_5327_, 9);
lean_inc_ref(v_extensions_5328_);
lean_dec(v___x_5327_);
v_ref_5329_ = lean_ctor_get(v_a_5325_, 2);
v___x_5330_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5323_, v_extensions_5328_);
lean_dec_ref(v_extensions_5328_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5338_; 
v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5333_ = v___x_5330_;
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_a_5331_);
lean_dec(v___x_5330_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5336_; 
if (v_isShared_5334_ == 0)
{
v___x_5336_ = v___x_5333_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5331_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5350_; 
v_a_5339_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5341_ = v___x_5330_;
v_isShared_5342_ = v_isSharedCheck_5350_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5330_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5350_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
v___x_5343_ = lean_io_error_to_string(v_a_5339_);
v___x_5344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5344_, 0, v___x_5343_);
v___x_5345_ = l_Lean_MessageData_ofFormat(v___x_5344_);
lean_inc(v_ref_5329_);
v___x_5346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5346_, 0, v_ref_5329_);
lean_ctor_set(v___x_5346_, 1, v___x_5345_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v___x_5346_);
v___x_5348_ = v___x_5341_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5351_, v_a_5352_, v_a_5353_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_ext_5351_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_5356_, lean_object* v_ext_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5357_, v_a_5359_, v_a_5362_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_5366_, lean_object* v_ext_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_5366_, v_ext_5367_, v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
lean_dec(v_a_5373_);
lean_dec_ref(v_a_5372_);
lean_dec(v_a_5371_);
lean_dec_ref(v_a_5370_);
lean_dec(v_a_5369_);
lean_dec_ref(v_a_5368_);
lean_dec_ref(v_ext_5367_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_5376_, lean_object* v_f_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v___x_5380_; lean_object* v_share_5381_; lean_object* v_maxFVar_5382_; lean_object* v_proofInstInfo_5383_; lean_object* v_proofInstInfoFVar_5384_; lean_object* v_letValue_5385_; lean_object* v_inferType_5386_; lean_object* v_getLevel_5387_; lean_object* v_congrInfo_5388_; lean_object* v_defEqI_5389_; lean_object* v_extensions_5390_; lean_object* v_issues_5391_; lean_object* v_canon_5392_; lean_object* v_instanceOverrides_5393_; uint8_t v_debug_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5413_; 
v___x_5380_ = lean_st_ref_take(v_a_5378_);
v_share_5381_ = lean_ctor_get(v___x_5380_, 0);
v_maxFVar_5382_ = lean_ctor_get(v___x_5380_, 1);
v_proofInstInfo_5383_ = lean_ctor_get(v___x_5380_, 2);
v_proofInstInfoFVar_5384_ = lean_ctor_get(v___x_5380_, 3);
v_letValue_5385_ = lean_ctor_get(v___x_5380_, 4);
v_inferType_5386_ = lean_ctor_get(v___x_5380_, 5);
v_getLevel_5387_ = lean_ctor_get(v___x_5380_, 6);
v_congrInfo_5388_ = lean_ctor_get(v___x_5380_, 7);
v_defEqI_5389_ = lean_ctor_get(v___x_5380_, 8);
v_extensions_5390_ = lean_ctor_get(v___x_5380_, 9);
v_issues_5391_ = lean_ctor_get(v___x_5380_, 10);
v_canon_5392_ = lean_ctor_get(v___x_5380_, 11);
v_instanceOverrides_5393_ = lean_ctor_get(v___x_5380_, 12);
v_debug_5394_ = lean_ctor_get_uint8(v___x_5380_, sizeof(void*)*13);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5380_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5396_ = v___x_5380_;
v_isShared_5397_ = v_isSharedCheck_5413_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_instanceOverrides_5393_);
lean_inc(v_canon_5392_);
lean_inc(v_issues_5391_);
lean_inc(v_extensions_5390_);
lean_inc(v_defEqI_5389_);
lean_inc(v_congrInfo_5388_);
lean_inc(v_getLevel_5387_);
lean_inc(v_inferType_5386_);
lean_inc(v_letValue_5385_);
lean_inc(v_proofInstInfoFVar_5384_);
lean_inc(v_proofInstInfo_5383_);
lean_inc(v_maxFVar_5382_);
lean_inc(v_share_5381_);
lean_dec(v___x_5380_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5413_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v_id_5398_; lean_object* v___x_5399_; lean_object* v___y_5401_; lean_object* v___x_5407_; uint8_t v___x_5408_; 
v_id_5398_ = lean_ctor_get(v_ext_5376_, 0);
v___x_5399_ = lean_box(0);
v___x_5407_ = lean_array_get_size(v_extensions_5390_);
v___x_5408_ = lean_nat_dec_lt(v_id_5398_, v___x_5407_);
if (v___x_5408_ == 0)
{
lean_dec(v_f_5377_);
v___y_5401_ = v_extensions_5390_;
goto v___jp_5400_;
}
else
{
lean_object* v_v_5409_; lean_object* v_xs_x27_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v_v_5409_ = lean_array_fget(v_extensions_5390_, v_id_5398_);
v_xs_x27_5410_ = lean_array_fset(v_extensions_5390_, v_id_5398_, v___x_5399_);
v___x_5411_ = lean_apply_1(v_f_5377_, v_v_5409_);
v___x_5412_ = lean_array_fset(v_xs_x27_5410_, v_id_5398_, v___x_5411_);
v___y_5401_ = v___x_5412_;
goto v___jp_5400_;
}
v___jp_5400_:
{
lean_object* v___x_5403_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 9, v___y_5401_);
v___x_5403_ = v___x_5396_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_share_5381_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_maxFVar_5382_);
lean_ctor_set(v_reuseFailAlloc_5406_, 2, v_proofInstInfo_5383_);
lean_ctor_set(v_reuseFailAlloc_5406_, 3, v_proofInstInfoFVar_5384_);
lean_ctor_set(v_reuseFailAlloc_5406_, 4, v_letValue_5385_);
lean_ctor_set(v_reuseFailAlloc_5406_, 5, v_inferType_5386_);
lean_ctor_set(v_reuseFailAlloc_5406_, 6, v_getLevel_5387_);
lean_ctor_set(v_reuseFailAlloc_5406_, 7, v_congrInfo_5388_);
lean_ctor_set(v_reuseFailAlloc_5406_, 8, v_defEqI_5389_);
lean_ctor_set(v_reuseFailAlloc_5406_, 9, v___y_5401_);
lean_ctor_set(v_reuseFailAlloc_5406_, 10, v_issues_5391_);
lean_ctor_set(v_reuseFailAlloc_5406_, 11, v_canon_5392_);
lean_ctor_set(v_reuseFailAlloc_5406_, 12, v_instanceOverrides_5393_);
lean_ctor_set_uint8(v_reuseFailAlloc_5406_, sizeof(void*)*13, v_debug_5394_);
v___x_5403_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5404_ = lean_st_ref_put(v_a_5378_, v___x_5403_);
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5399_);
return v___x_5405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_5414_, lean_object* v_f_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5414_, v_f_5415_, v_a_5416_);
lean_dec(v_a_5416_);
lean_dec_ref(v_ext_5414_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_5419_, lean_object* v_ext_5420_, lean_object* v_f_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v___x_5429_; 
v___x_5429_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5420_, v_f_5421_, v_a_5423_);
return v___x_5429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5430_, lean_object* v_ext_5431_, lean_object* v_f_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5430_, v_ext_5431_, v_f_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec_ref(v_ext_5431_);
return v_res_5440_;
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
