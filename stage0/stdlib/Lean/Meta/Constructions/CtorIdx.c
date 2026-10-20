// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Linter.Deprecated import Lean.Compiler.ImplementedByAttr import Lean.Compiler.LCNF.Util
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBuiltinType(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 119, 104, 54, 230, 159, 208, 234)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 246, 214, 203, 234, 6, 143, 204)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 215, 55, 153, 7, 83, 44, 161)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(35, 209, 53, 49, 90, 19, 84, 123)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
static const lean_string_object l_Lean_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_mkCtorIdxName___closed__0 = (const lean_object*)&l_Lean_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "getObjTagNat"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 128, 56, 123, 191, 118, 73, 69)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.mkCtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_Lean_mkCtorIdx___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__1;
static const lean_string_object l_Lean_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_mkCtorIdx___closed__2 = (const lean_object*)&l_Lean_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_76_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object* v_indName_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_82_ = l_Lean_Name_str___override(v_indName_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(lean_object* v_indName_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = l_Lean_mkCtorIdxName(v_indName_84_);
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0));
v___x_87_ = l_Lean_Name_str___override(v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object* v_env_88_, lean_object* v_declName_89_){
_start:
{
if (lean_obj_tag(v_declName_89_) == 1)
{
lean_object* v_pre_90_; lean_object* v_str_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_pre_90_ = lean_ctor_get(v_declName_89_, 0);
lean_inc(v_pre_90_);
v_str_91_ = lean_ctor_get(v_declName_89_, 1);
lean_inc_ref(v_str_91_);
lean_dec_ref_known(v_declName_89_, 2);
v___x_92_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_93_ = lean_string_dec_eq(v_str_91_, v___x_92_);
lean_dec_ref(v_str_91_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v_pre_90_);
lean_dec_ref(v_env_88_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_isInductiveCore_x3f(v_env_88_, v_pre_90_);
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_declName_89_);
lean_dec_ref(v_env_88_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object* v_declName_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v_env_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_st_ref_get(v_a_98_);
v_env_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_env_101_);
lean_dec(v___x_100_);
v___x_102_ = l_Lean_isCtorIdxCore_x3f(v_env_101_, v_declName_97_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_104_, v_a_105_);
lean_dec(v_a_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object* v_declName_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_108_, v_a_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object* v_declName_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_isCtorIdx_x3f(v_declName_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(lean_object* v_k_122_, lean_object* v_b_123_, lean_object* v_c_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
v___x_130_ = lean_apply_7(v_k_122_, v_b_123_, v_c_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed(lean_object* v_k_131_, lean_object* v_b_132_, lean_object* v_c_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(v_k_131_, v_b_132_, v_c_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(lean_object* v_type_140_, lean_object* v_k_141_, uint8_t v_cleanupAnnotations_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___f_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_148_, 0, v_k_141_);
v___x_149_ = 0;
v___x_150_ = lean_box(0);
v___x_151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_149_, v___x_150_, v_type_140_, v___f_148_, v_cleanupAnnotations_142_, v___x_149_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_151_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_151_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___boxed(lean_object* v_type_168_, lean_object* v_k_169_, lean_object* v_cleanupAnnotations_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_176_; lean_object* v_res_177_; 
v_cleanupAnnotations_boxed_176_ = lean_unbox(v_cleanupAnnotations_170_);
v_res_177_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_168_, v_k_169_, v_cleanupAnnotations_boxed_176_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(lean_object* v_00_u03b1_178_, lean_object* v_type_179_, lean_object* v_k_180_, uint8_t v_cleanupAnnotations_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_179_, v_k_180_, v_cleanupAnnotations_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___boxed(lean_object* v_00_u03b1_188_, lean_object* v_type_189_, lean_object* v_k_190_, lean_object* v_cleanupAnnotations_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_197_; lean_object* v_res_198_; 
v_cleanupAnnotations_boxed_197_ = lean_unbox(v_cleanupAnnotations_191_);
v_res_198_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(v_00_u03b1_188_, v_type_189_, v_k_190_, v_cleanupAnnotations_boxed_197_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(lean_object* v___x_202_, lean_object* v_args_203_, lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_discr_213_; lean_object* v___x_214_; 
v___x_210_ = lean_array_get_size(v_args_203_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v___x_210_, v___x_211_);
v_discr_213_ = lean_array_get_borrowed(v___x_202_, v_args_203_, v___x_212_);
lean_dec(v___x_212_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v_discr_213_);
v___x_214_ = lean_infer_type(v_discr_213_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_n(v_a_215_, 2);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = l_Lean_Meta_getLevel(v_a_215_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1));
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v_a_217_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = l_Lean_mkConst(v___x_218_, v___x_220_);
lean_inc(v_discr_213_);
v___x_222_ = l_Lean_mkAppB(v___x_221_, v_a_215_, v_discr_213_);
v___x_223_ = 0;
v___x_224_ = 1;
v___x_225_ = 1;
v___x_226_ = l_Lean_Meta_mkLambdaFVars(v_args_203_, v___x_222_, v___x_223_, v___x_224_, v___x_223_, v___x_224_, v___x_225_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v___x_226_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_215_);
v_a_227_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_216_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_216_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed(lean_object* v___x_235_, lean_object* v_args_236_, lean_object* v_x_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(v___x_235_, v_args_236_, v_x_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_args_236_);
lean_dec_ref(v___x_235_);
return v_res_243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0(void){
_start:
{
lean_object* v___x_244_; lean_object* v___f_245_; 
v___x_244_ = l_Lean_instInhabitedExpr;
v___f_245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed), 8, 1);
lean_closure_set(v___f_245_, 0, v___x_244_);
return v___f_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
v___x_252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v___x_251_);
lean_ctor_set(v___x_252_, 3, v___x_251_);
lean_ctor_set(v___x_252_, 4, v___x_251_);
lean_ctor_set(v___x_252_, 5, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object* v_indName_253_, lean_object* v_levelParams_254_, lean_object* v_declType_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___f_261_; lean_object* v_implName_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___f_261_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0);
lean_inc(v_indName_253_);
v_implName_262_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(v_indName_253_);
v___x_263_ = 0;
lean_inc_ref(v_declType_255_);
v___x_264_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_declType_255_, v___f_261_, v___x_263_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___x_306_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
lean_inc_n(v_implName_262_, 2);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v_implName_262_);
lean_ctor_set(v___x_266_, 1, v_levelParams_254_);
lean_ctor_set(v___x_266_, 2, v_declType_255_);
v___x_267_ = lean_box(0);
v___x_268_ = 0;
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v_implName_262_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_271_, 0, v___x_266_);
lean_ctor_set(v___x_271_, 1, v_a_265_);
lean_ctor_set(v___x_271_, 2, v___x_267_);
lean_ctor_set(v___x_271_, 3, v___x_270_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*4, v___x_268_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_inc_ref(v___x_272_);
v___x_306_ = l_Lean_addDecl(v___x_272_, v___x_263_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; lean_object* v_env_308_; lean_object* v_nextMacroScope_309_; lean_object* v_ngen_310_; lean_object* v_auxDeclNGen_311_; lean_object* v_traceState_312_; lean_object* v_recordedDeps_313_; lean_object* v_messages_314_; lean_object* v_infoState_315_; lean_object* v_snapshotTasks_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = lean_st_ref_take(v_a_259_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
v_nextMacroScope_309_ = lean_ctor_get(v___x_307_, 1);
v_ngen_310_ = lean_ctor_get(v___x_307_, 2);
v_auxDeclNGen_311_ = lean_ctor_get(v___x_307_, 3);
v_traceState_312_ = lean_ctor_get(v___x_307_, 4);
v_recordedDeps_313_ = lean_ctor_get(v___x_307_, 6);
v_messages_314_ = lean_ctor_get(v___x_307_, 7);
v_infoState_315_ = lean_ctor_get(v___x_307_, 8);
v_snapshotTasks_316_ = lean_ctor_get(v___x_307_, 9);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_307_, 5);
lean_dec(v_unused_413_);
v___x_318_ = v___x_307_;
v_isShared_319_ = v_isSharedCheck_412_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_snapshotTasks_316_);
lean_inc(v_infoState_315_);
lean_inc(v_messages_314_);
lean_inc(v_recordedDeps_313_);
lean_inc(v_traceState_312_);
lean_inc(v_auxDeclNGen_311_);
lean_inc(v_ngen_310_);
lean_inc(v_nextMacroScope_309_);
lean_inc(v_env_308_);
lean_dec(v___x_307_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_412_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_inc(v_implName_262_);
v___x_320_ = l_Lean_Meta_addToCompletionBlackList(v_env_308_, v_implName_262_);
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 5, v___x_321_);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_309_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_310_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_311_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_traceState_312_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_recordedDeps_313_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_messages_314_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_infoState_315_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_snapshotTasks_316_);
v___x_323_ = v_reuseFailAlloc_411_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_mctx_326_; lean_object* v_zetaDeltaFVarIds_327_; lean_object* v_postponed_328_; lean_object* v_diag_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_409_; 
v___x_324_ = lean_st_ref_put(v_a_259_, v___x_323_);
v___x_325_ = lean_st_ref_take(v_a_257_);
v_mctx_326_ = lean_ctor_get(v___x_325_, 0);
v_zetaDeltaFVarIds_327_ = lean_ctor_get(v___x_325_, 2);
v_postponed_328_ = lean_ctor_get(v___x_325_, 3);
v_diag_329_ = lean_ctor_get(v___x_325_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_325_, 1);
lean_dec(v_unused_410_);
v___x_331_ = v___x_325_;
v_isShared_332_ = v_isSharedCheck_409_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_diag_329_);
lean_inc(v_postponed_328_);
lean_inc(v_zetaDeltaFVarIds_327_);
lean_inc(v_mctx_326_);
lean_dec(v___x_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_409_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_mctx_326_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_327_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_328_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_329_);
v___x_335_ = v_reuseFailAlloc_408_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_traceState_342_; lean_object* v_recordedDeps_343_; lean_object* v_messages_344_; lean_object* v_infoState_345_; lean_object* v_snapshotTasks_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_406_; 
v___x_336_ = lean_st_ref_put(v_a_257_, v___x_335_);
v___x_337_ = lean_st_ref_take(v_a_259_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_337_, 1);
v_ngen_340_ = lean_ctor_get(v___x_337_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_337_, 3);
v_traceState_342_ = lean_ctor_get(v___x_337_, 4);
v_recordedDeps_343_ = lean_ctor_get(v___x_337_, 6);
v_messages_344_ = lean_ctor_get(v___x_337_, 7);
v_infoState_345_ = lean_ctor_get(v___x_337_, 8);
v_snapshotTasks_346_ = lean_ctor_get(v___x_337_, 9);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_337_, 5);
lean_dec(v_unused_407_);
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_406_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snapshotTasks_346_);
lean_inc(v_infoState_345_);
lean_inc(v_messages_344_);
lean_inc(v_recordedDeps_343_);
lean_inc(v_traceState_342_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_406_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
lean_inc(v_implName_262_);
v___x_350_ = l_Lean_addProtected(v_env_338_, v_implName_262_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 5, v___x_321_);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_traceState_342_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_recordedDeps_343_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_messages_344_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_infoState_345_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_snapshotTasks_346_);
v___x_352_ = v_reuseFailAlloc_405_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_mctx_355_; lean_object* v_zetaDeltaFVarIds_356_; lean_object* v_postponed_357_; lean_object* v_diag_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_403_; 
v___x_353_ = lean_st_ref_put(v_a_259_, v___x_352_);
v___x_354_ = lean_st_ref_take(v_a_257_);
v_mctx_355_ = lean_ctor_get(v___x_354_, 0);
v_zetaDeltaFVarIds_356_ = lean_ctor_get(v___x_354_, 2);
v_postponed_357_ = lean_ctor_get(v___x_354_, 3);
v_diag_358_ = lean_ctor_get(v___x_354_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_354_, 1);
lean_dec(v_unused_404_);
v___x_360_ = v___x_354_;
v_isShared_361_ = v_isSharedCheck_403_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_diag_358_);
lean_inc(v_postponed_357_);
lean_inc(v_zetaDeltaFVarIds_356_);
lean_inc(v_mctx_355_);
lean_dec(v___x_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_403_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_333_);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_mctx_355_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_zetaDeltaFVarIds_356_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_postponed_357_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_diag_358_);
v___x_363_ = v_reuseFailAlloc_402_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_env_366_; uint8_t v___x_367_; 
v___x_364_ = lean_st_ref_put(v_a_257_, v___x_363_);
v___x_365_ = lean_st_ref_get(v_a_259_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = l_Lean_isMarkedMeta(v_env_366_, v_indName_253_);
if (v___x_367_ == 0)
{
v___y_274_ = v_a_256_;
v___y_275_ = v_a_257_;
v___y_276_ = v_a_258_;
v___y_277_ = v_a_259_;
goto v___jp_273_;
}
else
{
lean_object* v___x_368_; lean_object* v_env_369_; lean_object* v_nextMacroScope_370_; lean_object* v_ngen_371_; lean_object* v_auxDeclNGen_372_; lean_object* v_traceState_373_; lean_object* v_recordedDeps_374_; lean_object* v_messages_375_; lean_object* v_infoState_376_; lean_object* v_snapshotTasks_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_400_; 
v___x_368_ = lean_st_ref_take(v_a_259_);
v_env_369_ = lean_ctor_get(v___x_368_, 0);
v_nextMacroScope_370_ = lean_ctor_get(v___x_368_, 1);
v_ngen_371_ = lean_ctor_get(v___x_368_, 2);
v_auxDeclNGen_372_ = lean_ctor_get(v___x_368_, 3);
v_traceState_373_ = lean_ctor_get(v___x_368_, 4);
v_recordedDeps_374_ = lean_ctor_get(v___x_368_, 6);
v_messages_375_ = lean_ctor_get(v___x_368_, 7);
v_infoState_376_ = lean_ctor_get(v___x_368_, 8);
v_snapshotTasks_377_ = lean_ctor_get(v___x_368_, 9);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v___x_368_, 5);
lean_dec(v_unused_401_);
v___x_379_ = v___x_368_;
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_snapshotTasks_377_);
lean_inc(v_infoState_376_);
lean_inc(v_messages_375_);
lean_inc(v_recordedDeps_374_);
lean_inc(v_traceState_373_);
lean_inc(v_auxDeclNGen_372_);
lean_inc(v_ngen_371_);
lean_inc(v_nextMacroScope_370_);
lean_inc(v_env_369_);
lean_dec(v___x_368_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc(v_implName_262_);
v___x_381_ = l_Lean_markMeta(v_env_369_, v_implName_262_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 5, v___x_321_);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextMacroScope_370_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_ngen_371_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_auxDeclNGen_372_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_traceState_373_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v_recordedDeps_374_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_messages_375_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_infoState_376_);
lean_ctor_set(v_reuseFailAlloc_399_, 9, v_snapshotTasks_377_);
v___x_383_ = v_reuseFailAlloc_399_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_mctx_386_; lean_object* v_zetaDeltaFVarIds_387_; lean_object* v_postponed_388_; lean_object* v_diag_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v___x_384_ = lean_st_ref_put(v_a_259_, v___x_383_);
v___x_385_ = lean_st_ref_take(v_a_257_);
v_mctx_386_ = lean_ctor_get(v___x_385_, 0);
v_zetaDeltaFVarIds_387_ = lean_ctor_get(v___x_385_, 2);
v_postponed_388_ = lean_ctor_get(v___x_385_, 3);
v_diag_389_ = lean_ctor_get(v___x_385_, 4);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_385_, 1);
lean_dec(v_unused_398_);
v___x_391_ = v___x_385_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_diag_389_);
lean_inc(v_postponed_388_);
lean_inc(v_zetaDeltaFVarIds_387_);
lean_inc(v_mctx_386_);
lean_dec(v___x_385_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_333_);
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_mctx_386_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_zetaDeltaFVarIds_387_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_postponed_388_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_diag_389_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_st_ref_put(v_a_257_, v___x_394_);
v___y_274_ = v_a_256_;
v___y_275_ = v_a_257_;
v___y_276_ = v_a_258_;
v___y_277_ = v_a_259_;
goto v___jp_273_;
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
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref_known(v___x_272_, 1);
lean_dec(v_implName_262_);
lean_dec(v_indName_253_);
v_a_414_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_306_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_306_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
v___jp_273_:
{
uint8_t v___x_278_; lean_object* v___x_279_; 
v___x_278_ = 4;
lean_inc(v_implName_262_);
v___x_279_ = l_Lean_Meta_setInlineAttribute(v_implName_262_, v___x_278_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_279_) == 0)
{
uint8_t v___x_280_; lean_object* v___x_281_; 
lean_dec_ref_known(v___x_279_, 1);
v___x_280_ = 1;
v___x_281_ = l_Lean_compileDecl(v___x_272_, v___x_280_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_289_);
v___x_283_ = v___x_281_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___x_281_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_implName_262_);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_implName_262_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_implName_262_);
v_a_290_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_281_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_281_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref_known(v___x_272_, 1);
lean_dec(v_implName_262_);
v_a_298_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_279_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_279_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_implName_262_);
lean_dec_ref(v_declType_255_);
lean_dec(v_levelParams_254_);
lean_dec(v_indName_253_);
v_a_422_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_264_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_264_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object* v_indName_430_, lean_object* v_levelParams_431_, lean_object* v_declType_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_430_, v_levelParams_431_, v_declType_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object* v_opts_439_, lean_object* v_opt_440_){
_start:
{
lean_object* v_name_441_; lean_object* v_defValue_442_; lean_object* v_map_443_; lean_object* v___x_444_; 
v_name_441_ = lean_ctor_get(v_opt_440_, 0);
v_defValue_442_ = lean_ctor_get(v_opt_440_, 1);
v_map_443_ = lean_ctor_get(v_opts_439_, 0);
v___x_444_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_443_, v_name_441_);
if (lean_obj_tag(v___x_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = lean_unbox(v_defValue_442_);
return v___x_445_;
}
else
{
lean_object* v_val_446_; 
v_val_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_444_, 1);
if (lean_obj_tag(v_val_446_) == 1)
{
uint8_t v_v_447_; 
v_v_447_ = lean_ctor_get_uint8(v_val_446_, 0);
lean_dec_ref_known(v_val_446_, 0);
return v_v_447_;
}
else
{
uint8_t v___x_448_; 
lean_dec(v_val_446_);
v___x_448_ = lean_unbox(v_defValue_442_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object* v_opts_449_, lean_object* v_opt_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_449_, v_opt_450_);
lean_dec_ref(v_opt_450_);
lean_dec_ref(v_opts_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object* v_constName_453_, uint8_t v_skipRealize_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v_env_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = lean_st_ref_get(v___y_455_);
v_env_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_env_458_);
lean_dec(v___x_457_);
v___x_459_ = l_Lean_Environment_contains(v_env_458_, v_constName_453_, v_skipRealize_454_);
v___x_460_ = lean_box(v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_462_, lean_object* v_skipRealize_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v_skipRealize_boxed_466_; lean_object* v_res_467_; 
v_skipRealize_boxed_466_ = lean_unbox(v_skipRealize_463_);
v_res_467_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_462_, v_skipRealize_boxed_466_, v___y_464_);
lean_dec(v___y_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object* v_constName_468_, uint8_t v_skipRealize_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_468_, v_skipRealize_469_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object* v_constName_476_, lean_object* v_skipRealize_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
uint8_t v_skipRealize_boxed_483_; lean_object* v_res_484_; 
v_skipRealize_boxed_483_ = lean_unbox(v_skipRealize_477_);
v_res_484_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_476_, v_skipRealize_boxed_483_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object* v_type_485_, lean_object* v_maxFVars_x3f_486_, lean_object* v_k_487_, uint8_t v_cleanupAnnotations_488_, uint8_t v_whnfType_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; 
v___f_495_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_495_, 0, v_k_487_);
v___x_496_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_485_, v_maxFVars_x3f_486_, v___f_495_, v_cleanupAnnotations_488_, v_whnfType_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_496_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_496_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_513_, lean_object* v_maxFVars_x3f_514_, lean_object* v_k_515_, lean_object* v_cleanupAnnotations_516_, lean_object* v_whnfType_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_523_; uint8_t v_whnfType_boxed_524_; lean_object* v_res_525_; 
v_cleanupAnnotations_boxed_523_ = lean_unbox(v_cleanupAnnotations_516_);
v_whnfType_boxed_524_ = lean_unbox(v_whnfType_517_);
v_res_525_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_513_, v_maxFVars_x3f_514_, v_k_515_, v_cleanupAnnotations_boxed_523_, v_whnfType_boxed_524_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object* v_00_u03b1_526_, lean_object* v_type_527_, lean_object* v_maxFVars_x3f_528_, lean_object* v_k_529_, uint8_t v_cleanupAnnotations_530_, uint8_t v_whnfType_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_527_, v_maxFVars_x3f_528_, v_k_529_, v_cleanupAnnotations_530_, v_whnfType_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_538_, lean_object* v_type_539_, lean_object* v_maxFVars_x3f_540_, lean_object* v_k_541_, lean_object* v_cleanupAnnotations_542_, lean_object* v_whnfType_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_549_; uint8_t v_whnfType_boxed_550_; lean_object* v_res_551_; 
v_cleanupAnnotations_boxed_549_ = lean_unbox(v_cleanupAnnotations_542_);
v_whnfType_boxed_550_ = lean_unbox(v_whnfType_543_);
v_res_551_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(v_00_u03b1_538_, v_type_539_, v_maxFVars_x3f_540_, v_k_541_, v_cleanupAnnotations_boxed_549_, v_whnfType_boxed_550_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object* v_name_552_, lean_object* v_levelParams_553_, lean_object* v_type_554_, lean_object* v_value_555_, lean_object* v_hints_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; uint8_t v___y_561_; lean_object* v_env_569_; uint8_t v___x_570_; 
v___x_559_ = lean_st_ref_get(v___y_557_);
v_env_569_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref_n(v_env_569_, 2);
lean_dec(v___x_559_);
v___x_570_ = l_Lean_Environment_hasUnsafe(v_env_569_, v_type_554_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; 
v___x_571_ = l_Lean_Environment_hasUnsafe(v_env_569_, v_value_555_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
v___x_572_ = 1;
v___y_561_ = v___x_572_;
goto v___jp_560_;
}
else
{
goto v___jp_567_;
}
}
else
{
lean_dec_ref(v_env_569_);
goto v___jp_567_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_inc(v_name_552_);
v___x_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_562_, 0, v_name_552_);
lean_ctor_set(v___x_562_, 1, v_levelParams_553_);
lean_ctor_set(v___x_562_, 2, v_type_554_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v_name_552_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_565_, 0, v___x_562_);
lean_ctor_set(v___x_565_, 1, v_value_555_);
lean_ctor_set(v___x_565_, 2, v_hints_556_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*4, v___y_561_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
v___jp_567_:
{
uint8_t v___x_568_; 
v___x_568_ = 0;
v___y_561_ = v___x_568_;
goto v___jp_560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_573_, lean_object* v_levelParams_574_, lean_object* v_type_575_, lean_object* v_value_576_, lean_object* v_hints_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_573_, v_levelParams_574_, v_type_575_, v_value_576_, v_hints_577_, v___y_578_);
lean_dec(v___y_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object* v_name_581_, lean_object* v_levelParams_582_, lean_object* v_type_583_, lean_object* v_value_584_, lean_object* v_hints_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_581_, v_levelParams_582_, v_type_583_, v_value_584_, v_hints_585_, v___y_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object* v_name_592_, lean_object* v_levelParams_593_, lean_object* v_type_594_, lean_object* v_value_595_, lean_object* v_hints_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_592_, v_levelParams_593_, v_type_594_, v_value_595_, v_hints_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11(lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___f_610_; lean_object* v___x_12992__overap_611_; lean_object* v___x_612_; 
v___f_610_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0));
v___x_12992__overap_611_ = lean_panic_fn_borrowed(v___f_610_, v_msg_604_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
v___x_612_ = lean_apply_5(v___x_12992__overap_611_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v_msg_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object* v___y_620_, uint8_t v_isExporting_621_, lean_object* v___x_622_, lean_object* v___y_623_, lean_object* v___x_624_, lean_object* v_a_x3f_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_env_628_; lean_object* v_nextMacroScope_629_; lean_object* v_ngen_630_; lean_object* v_auxDeclNGen_631_; lean_object* v_traceState_632_; lean_object* v_recordedDeps_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_661_; 
v___x_627_ = lean_st_ref_take(v___y_620_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
v_nextMacroScope_629_ = lean_ctor_get(v___x_627_, 1);
v_ngen_630_ = lean_ctor_get(v___x_627_, 2);
v_auxDeclNGen_631_ = lean_ctor_get(v___x_627_, 3);
v_traceState_632_ = lean_ctor_get(v___x_627_, 4);
v_recordedDeps_633_ = lean_ctor_get(v___x_627_, 6);
v_messages_634_ = lean_ctor_get(v___x_627_, 7);
v_infoState_635_ = lean_ctor_get(v___x_627_, 8);
v_snapshotTasks_636_ = lean_ctor_get(v___x_627_, 9);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_627_, 5);
lean_dec(v_unused_662_);
v___x_638_ = v___x_627_;
v_isShared_639_ = v_isSharedCheck_661_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snapshotTasks_636_);
lean_inc(v_infoState_635_);
lean_inc(v_messages_634_);
lean_inc(v_recordedDeps_633_);
lean_inc(v_traceState_632_);
lean_inc(v_auxDeclNGen_631_);
lean_inc(v_ngen_630_);
lean_inc(v_nextMacroScope_629_);
lean_inc(v_env_628_);
lean_dec(v___x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_661_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = l_Lean_Environment_setExporting(v_env_628_, v_isExporting_621_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 5, v___x_622_);
lean_ctor_set(v___x_638_, 0, v___x_640_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_nextMacroScope_629_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_ngen_630_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v_auxDeclNGen_631_);
lean_ctor_set(v_reuseFailAlloc_660_, 4, v_traceState_632_);
lean_ctor_set(v_reuseFailAlloc_660_, 5, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_660_, 6, v_recordedDeps_633_);
lean_ctor_set(v_reuseFailAlloc_660_, 7, v_messages_634_);
lean_ctor_set(v_reuseFailAlloc_660_, 8, v_infoState_635_);
lean_ctor_set(v_reuseFailAlloc_660_, 9, v_snapshotTasks_636_);
v___x_642_ = v_reuseFailAlloc_660_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_mctx_645_; lean_object* v_zetaDeltaFVarIds_646_; lean_object* v_postponed_647_; lean_object* v_diag_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_658_; 
v___x_643_ = lean_st_ref_put(v___y_620_, v___x_642_);
v___x_644_ = lean_st_ref_take(v___y_623_);
v_mctx_645_ = lean_ctor_get(v___x_644_, 0);
v_zetaDeltaFVarIds_646_ = lean_ctor_get(v___x_644_, 2);
v_postponed_647_ = lean_ctor_get(v___x_644_, 3);
v_diag_648_ = lean_ctor_get(v___x_644_, 4);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v___x_644_, 1);
lean_dec(v_unused_659_);
v___x_650_ = v___x_644_;
v_isShared_651_ = v_isSharedCheck_658_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_diag_648_);
lean_inc(v_postponed_647_);
lean_inc(v_zetaDeltaFVarIds_646_);
lean_inc(v_mctx_645_);
lean_dec(v___x_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_658_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = lean_box(0);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_624_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_mctx_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_zetaDeltaFVarIds_646_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_postponed_647_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v_diag_648_);
v___x_654_ = v_reuseFailAlloc_657_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_st_ref_put(v___y_623_, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_652_);
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object* v___y_663_, lean_object* v_isExporting_664_, lean_object* v___x_665_, lean_object* v___y_666_, lean_object* v___x_667_, lean_object* v_a_x3f_668_, lean_object* v___y_669_){
_start:
{
uint8_t v_isExporting_boxed_670_; lean_object* v_res_671_; 
v_isExporting_boxed_670_ = lean_unbox(v_isExporting_664_);
v_res_671_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_663_, v_isExporting_boxed_670_, v___x_665_, v___y_666_, v___x_667_, v_a_x3f_668_);
lean_dec(v_a_x3f_668_);
lean_dec(v___y_666_);
lean_dec(v___y_663_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_x_672_, uint8_t v_isExporting_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v_env_680_; lean_object* v___x_681_; uint8_t v_isModule_682_; 
v___x_679_ = lean_st_ref_get(v___y_677_);
v_env_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_ref(v_env_680_);
lean_dec(v___x_679_);
v___x_681_ = l_Lean_Environment_header(v_env_680_);
v_isModule_682_ = lean_ctor_get_uint8(v___x_681_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_681_);
if (v_isModule_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec_ref(v_env_680_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
v___x_683_ = lean_apply_5(v_x_672_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
return v___x_683_;
}
else
{
uint8_t v_isExporting_684_; 
v_isExporting_684_ = lean_ctor_get_uint8(v_env_680_, sizeof(void*)*13);
lean_dec_ref(v_env_680_);
if (v_isExporting_673_ == 0)
{
if (v_isExporting_684_ == 0)
{
lean_object* v___x_751_; 
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
v___x_751_ = lean_apply_5(v_x_672_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
return v___x_751_;
}
else
{
goto v___jp_685_;
}
}
else
{
if (v_isExporting_684_ == 0)
{
goto v___jp_685_;
}
else
{
lean_object* v___x_752_; 
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
v___x_752_ = lean_apply_5(v_x_672_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
return v___x_752_;
}
}
v___jp_685_:
{
lean_object* v___x_686_; lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_traceState_691_; lean_object* v_recordedDeps_692_; lean_object* v_messages_693_; lean_object* v_infoState_694_; lean_object* v_snapshotTasks_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_749_; 
v___x_686_ = lean_st_ref_take(v___y_677_);
v_env_687_ = lean_ctor_get(v___x_686_, 0);
v_nextMacroScope_688_ = lean_ctor_get(v___x_686_, 1);
v_ngen_689_ = lean_ctor_get(v___x_686_, 2);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_686_, 3);
v_traceState_691_ = lean_ctor_get(v___x_686_, 4);
v_recordedDeps_692_ = lean_ctor_get(v___x_686_, 6);
v_messages_693_ = lean_ctor_get(v___x_686_, 7);
v_infoState_694_ = lean_ctor_get(v___x_686_, 8);
v_snapshotTasks_695_ = lean_ctor_get(v___x_686_, 9);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_686_, 5);
lean_dec(v_unused_750_);
v___x_697_ = v___x_686_;
v_isShared_698_ = v_isSharedCheck_749_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snapshotTasks_695_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_693_);
lean_inc(v_recordedDeps_692_);
lean_inc(v_traceState_691_);
lean_inc(v_auxDeclNGen_690_);
lean_inc(v_ngen_689_);
lean_inc(v_nextMacroScope_688_);
lean_inc(v_env_687_);
lean_dec(v___x_686_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_749_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = l_Lean_Environment_setExporting(v_env_687_, v_isExporting_673_);
v___x_700_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 5, v___x_700_);
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_nextMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_ngen_689_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_traceState_691_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_recordedDeps_692_);
lean_ctor_set(v_reuseFailAlloc_748_, 7, v_messages_693_);
lean_ctor_set(v_reuseFailAlloc_748_, 8, v_infoState_694_);
lean_ctor_set(v_reuseFailAlloc_748_, 9, v_snapshotTasks_695_);
v___x_702_ = v_reuseFailAlloc_748_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_mctx_705_; lean_object* v_zetaDeltaFVarIds_706_; lean_object* v_postponed_707_; lean_object* v_diag_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_746_; 
v___x_703_ = lean_st_ref_put(v___y_677_, v___x_702_);
v___x_704_ = lean_st_ref_take(v___y_675_);
v_mctx_705_ = lean_ctor_get(v___x_704_, 0);
v_zetaDeltaFVarIds_706_ = lean_ctor_get(v___x_704_, 2);
v_postponed_707_ = lean_ctor_get(v___x_704_, 3);
v_diag_708_ = lean_ctor_get(v___x_704_, 4);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_704_, 1);
lean_dec(v_unused_747_);
v___x_710_ = v___x_704_;
v_isShared_711_ = v_isSharedCheck_746_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_diag_708_);
lean_inc(v_postponed_707_);
lean_inc(v_zetaDeltaFVarIds_706_);
lean_inc(v_mctx_705_);
lean_dec(v___x_704_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_746_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_mctx_705_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_zetaDeltaFVarIds_706_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_postponed_707_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_diag_708_);
v___x_714_ = v_reuseFailAlloc_745_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v_r_716_; 
v___x_715_ = lean_st_ref_put(v___y_675_, v___x_714_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
v_r_716_ = lean_apply_5(v_x_672_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v_r_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_733_; 
v_a_717_ = lean_ctor_get(v_r_716_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_r_716_);
if (v_isSharedCheck_733_ == 0)
{
v___x_719_ = v_r_716_;
v_isShared_720_ = v_isSharedCheck_733_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v_r_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_733_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
lean_inc(v_a_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 1);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_732_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v___x_723_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_677_, v_isExporting_684_, v___x_700_, v___y_675_, v___x_712_, v___x_722_);
lean_dec_ref(v___x_722_);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v___x_723_, 0);
lean_dec(v_unused_731_);
v___x_725_ = v___x_723_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_dec(v___x_723_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_a_717_);
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_717_);
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
else
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_734_ = lean_ctor_get(v_r_716_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v_r_716_, 1);
v___x_735_ = lean_box(0);
v___x_736_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_677_, v_isExporting_684_, v___x_700_, v___y_675_, v___x_712_, v___x_735_);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_736_, 0);
lean_dec(v_unused_744_);
v___x_738_ = v___x_736_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_dec(v___x_736_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 1);
lean_ctor_set(v___x_738_, 0, v_a_734_);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_734_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_x_753_, lean_object* v_isExporting_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v_isExporting_boxed_760_; lean_object* v_res_761_; 
v_isExporting_boxed_760_ = lean_unbox(v_isExporting_754_);
v_res_761_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_753_, v_isExporting_boxed_760_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object* v_00_u03b1_762_, lean_object* v_x_763_, uint8_t v_isExporting_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_763_, v_isExporting_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_771_, lean_object* v_x_772_, lean_object* v_isExporting_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v_isExporting_boxed_779_; lean_object* v_res_780_; 
v_isExporting_boxed_779_ = lean_unbox(v_isExporting_773_);
v_res_780_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(v_00_u03b1_771_, v_x_772_, v_isExporting_boxed_779_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_781_, uint8_t v___x_782_, uint8_t v___x_783_, uint8_t v___x_784_, lean_object* v_ys_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_Lean_mkRawNatLit(v_cidx_781_);
v___x_793_ = l_Lean_Meta_mkLambdaFVars(v_ys_785_, v___x_792_, v___x_782_, v___x_783_, v___x_782_, v___x_783_, v___x_784_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v_ys_798_, lean_object* v_x_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
uint8_t v___x_20192__boxed_805_; uint8_t v___x_20193__boxed_806_; uint8_t v___x_20194__boxed_807_; lean_object* v_res_808_; 
v___x_20192__boxed_805_ = lean_unbox(v___x_795_);
v___x_20193__boxed_806_ = lean_unbox(v___x_796_);
v___x_20194__boxed_807_ = lean_unbox(v___x_797_);
v_res_808_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_794_, v___x_20192__boxed_805_, v___x_20193__boxed_806_, v___x_20194__boxed_807_, v_ys_798_, v_x_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_x_799_);
lean_dec_ref(v_ys_798_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_env_816_; uint8_t v___x_817_; lean_object* v_env_818_; lean_object* v___x_819_; lean_object* v_toCold_820_; lean_object* v_mctx_821_; lean_object* v_lctx_822_; lean_object* v_options_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_815_ = lean_st_ref_get(v___y_813_);
v_env_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc_ref(v_env_816_);
lean_dec(v___x_815_);
v___x_817_ = 0;
v_env_818_ = l_Lean_Environment_setRecordingDeps(v_env_816_, v___x_817_);
v___x_819_ = lean_st_ref_get(v___y_811_);
v_toCold_820_ = lean_ctor_get(v___y_812_, 0);
v_mctx_821_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_mctx_821_);
lean_dec(v___x_819_);
v_lctx_822_ = lean_ctor_get(v___y_810_, 2);
v_options_823_ = lean_ctor_get(v_toCold_820_, 2);
lean_inc_ref(v_options_823_);
lean_inc_ref(v_lctx_822_);
v___x_824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_824_, 0, v_env_818_);
lean_ctor_set(v___x_824_, 1, v_mctx_821_);
lean_ctor_set(v___x_824_, 2, v_lctx_822_);
lean_ctor_set(v___x_824_, 3, v_options_823_);
v___x_825_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_msgData_809_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_ref_840_; lean_object* v___x_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_ref_840_ = lean_ctor_get(v___y_837_, 2);
v___x_841_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_inc(v_ref_840_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_ref_840_);
lean_ctor_set(v___x_846_, 1, v_a_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 1);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_857_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_instMonadEIO___redArg();
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_toApplicative_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_932_; 
v___x_869_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_870_ = l_StateRefT_x27_instMonad___redArg(v___x_869_);
v_toApplicative_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v___x_870_, 1);
lean_dec(v_unused_933_);
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_932_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_toApplicative_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_932_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_toFunctor_875_; lean_object* v_toSeq_876_; lean_object* v_toSeqLeft_877_; lean_object* v_toSeqRight_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_930_; 
v_toFunctor_875_ = lean_ctor_get(v_toApplicative_871_, 0);
v_toSeq_876_ = lean_ctor_get(v_toApplicative_871_, 2);
v_toSeqLeft_877_ = lean_ctor_get(v_toApplicative_871_, 3);
v_toSeqRight_878_ = lean_ctor_get(v_toApplicative_871_, 4);
v_isSharedCheck_930_ = !lean_is_exclusive(v_toApplicative_871_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_toApplicative_871_, 1);
lean_dec(v_unused_931_);
v___x_880_ = v_toApplicative_871_;
v_isShared_881_ = v_isSharedCheck_930_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_toSeqRight_878_);
lean_inc(v_toSeqLeft_877_);
lean_inc(v_toSeq_876_);
lean_inc(v_toFunctor_875_);
lean_dec(v_toApplicative_871_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_930_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___x_891_; 
v___f_882_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_883_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_875_);
v___f_884_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_884_, 0, v_toFunctor_875_);
v___f_885_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_885_, 0, v_toFunctor_875_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___f_884_);
lean_ctor_set(v___x_886_, 1, v___f_885_);
v___f_887_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_887_, 0, v_toSeqRight_878_);
v___f_888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_888_, 0, v_toSeqLeft_877_);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_889_, 0, v_toSeq_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 4, v___f_887_);
lean_ctor_set(v___x_880_, 3, v___f_888_);
lean_ctor_set(v___x_880_, 2, v___f_889_);
lean_ctor_set(v___x_880_, 1, v___f_882_);
lean_ctor_set(v___x_880_, 0, v___x_886_);
v___x_891_ = v___x_880_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___f_882_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v___f_889_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v___f_888_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v___f_887_);
v___x_891_ = v_reuseFailAlloc_929_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v___f_883_);
lean_ctor_set(v___x_873_, 0, v___x_891_);
v___x_893_ = v___x_873_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___f_883_);
v___x_893_ = v_reuseFailAlloc_928_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v_toApplicative_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_926_; 
v___x_894_ = l_StateRefT_x27_instMonad___redArg(v___x_893_);
v_toApplicative_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v___x_894_, 1);
lean_dec(v_unused_927_);
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_926_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_toApplicative_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_926_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_toFunctor_899_; lean_object* v_toSeq_900_; lean_object* v_toSeqLeft_901_; lean_object* v_toSeqRight_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_924_; 
v_toFunctor_899_ = lean_ctor_get(v_toApplicative_895_, 0);
v_toSeq_900_ = lean_ctor_get(v_toApplicative_895_, 2);
v_toSeqLeft_901_ = lean_ctor_get(v_toApplicative_895_, 3);
v_toSeqRight_902_ = lean_ctor_get(v_toApplicative_895_, 4);
v_isSharedCheck_924_ = !lean_is_exclusive(v_toApplicative_895_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v_toApplicative_895_, 1);
lean_dec(v_unused_925_);
v___x_904_ = v_toApplicative_895_;
v_isShared_905_ = v_isSharedCheck_924_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_toSeqRight_902_);
lean_inc(v_toSeqLeft_901_);
lean_inc(v_toSeq_900_);
lean_inc(v_toFunctor_899_);
lean_dec(v_toApplicative_895_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_924_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_915_; 
v___f_906_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_907_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_899_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_908_, 0, v_toFunctor_899_);
v___f_909_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_909_, 0, v_toFunctor_899_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___f_908_);
lean_ctor_set(v___x_910_, 1, v___f_909_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_911_, 0, v_toSeqRight_902_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_912_, 0, v_toSeqLeft_901_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_913_, 0, v_toSeq_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 4, v___f_911_);
lean_ctor_set(v___x_904_, 3, v___f_912_);
lean_ctor_set(v___x_904_, 2, v___f_913_);
lean_ctor_set(v___x_904_, 1, v___f_906_);
lean_ctor_set(v___x_904_, 0, v___x_910_);
v___x_915_ = v___x_904_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___f_906_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v___f_913_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v___f_912_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v___f_911_);
v___x_915_ = v_reuseFailAlloc_923_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___f_907_);
lean_ctor_set(v___x_897_, 0, v___x_915_);
v___x_917_ = v___x_897_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___f_907_);
v___x_917_ = v_reuseFailAlloc_922_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_16393__overap_920_; lean_object* v___x_921_; 
v___x_918_ = lean_box(0);
v___x_919_ = l_instInhabitedOfMonad___redArg(v___x_917_, v___x_918_);
v___x_16393__overap_920_ = lean_panic_fn_borrowed(v___x_919_, v_msg_863_);
lean_dec(v___x_919_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
v___x_921_ = lean_apply_5(v___x_16393__overap_920_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
return v___x_921_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_950_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_951_ = lean_unsigned_to_nat(11u);
v___x_952_ = lean_unsigned_to_nat(122u);
v___x_953_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_954_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_955_ = l_mkPanicMessageWithDecl(v___x_954_, v___x_953_, v___x_952_, v___x_951_, v___x_950_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v___x_970_ = lean_st_ref_get(v___y_960_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_970_);
v___x_972_ = 0;
lean_inc(v_constName_956_);
v___x_973_ = l_Lean_Environment_findAsync_x3f(v_env_971_, v_constName_956_, v___x_972_);
if (lean_obj_tag(v___x_973_) == 1)
{
lean_object* v_val_974_; uint8_t v_kind_975_; 
v_val_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v___x_973_, 1);
v_kind_975_ = lean_ctor_get_uint8(v_val_974_, sizeof(void*)*3);
if (v_kind_975_ == 6)
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_974_);
if (lean_obj_tag(v___x_976_) == 6)
{
lean_object* v_val_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_constName_956_);
v_val_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_val_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 0);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_val_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec_ref(v___x_976_);
v___x_985_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_986_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_985_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
if (lean_obj_tag(v_a_987_) == 0)
{
lean_del_object(v___x_989_);
goto v___jp_962_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_993_; 
lean_dec(v_constName_956_);
v_val_991_ = lean_ctor_get(v_a_987_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_a_987_, 1);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v_val_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_val_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_constName_956_);
v_a_996_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_986_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_986_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
else
{
lean_dec(v_val_974_);
goto v___jp_962_;
}
}
else
{
lean_dec(v___x_973_);
goto v___jp_962_;
}
v___jp_962_:
{
lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_963_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_964_ = 0;
v___x_965_ = l_Lean_MessageData_ofConstName(v_constName_956_, v___x_964_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_963_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_968_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_1011_, lean_object* v___x_1012_, lean_object* v_as_x27_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
if (lean_obj_tag(v_as_x27_1013_) == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_b_1014_);
return v___x_1020_;
}
else
{
lean_object* v_head_1021_; lean_object* v_tail_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; 
v_head_1021_ = lean_ctor_get(v_as_x27_1013_, 0);
v_tail_1022_ = lean_ctor_get(v_as_x27_1013_, 1);
v___x_1023_ = 0;
v___x_1024_ = 1;
lean_inc(v_head_1021_);
v___x_1025_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_1021_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_toConstantVal_1027_; lean_object* v_cidx_1028_; lean_object* v_numFields_1029_; lean_object* v_type_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_toConstantVal_1027_ = lean_ctor_get(v_a_1026_, 0);
lean_inc_ref(v_toConstantVal_1027_);
v_cidx_1028_ = lean_ctor_get(v_a_1026_, 2);
lean_inc(v_cidx_1028_);
v_numFields_1029_ = lean_ctor_get(v_a_1026_, 4);
lean_inc(v_numFields_1029_);
lean_dec(v_a_1026_);
v_type_1030_ = lean_ctor_get(v_toConstantVal_1027_, 2);
lean_inc_ref(v_type_1030_);
lean_dec_ref(v_toConstantVal_1027_);
v___x_1031_ = lean_box(v___x_1023_);
v___x_1032_ = lean_box(v___x_1011_);
v___x_1033_ = lean_box(v___x_1024_);
v___f_1034_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1034_, 0, v_cidx_1028_);
lean_closure_set(v___f_1034_, 1, v___x_1031_);
lean_closure_set(v___f_1034_, 2, v___x_1032_);
lean_closure_set(v___f_1034_, 3, v___x_1033_);
v___x_1035_ = l_Lean_Meta_instantiateForall(v_type_1030_, v___x_1012_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1047_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1047_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1047_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 0, v_numFields_1029_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_numFields_1029_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_1036_, v___x_1041_, v___f_1034_, v___x_1023_, v___x_1023_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = l_Lean_Expr_app___override(v_b_1014_, v_a_1043_);
v_as_x27_1013_ = v_tail_1022_;
v_b_1014_ = v___x_1044_;
goto _start;
}
else
{
lean_dec_ref(v_b_1014_);
return v___x_1042_;
}
}
}
}
else
{
lean_dec_ref(v___f_1034_);
lean_dec(v_numFields_1029_);
lean_dec_ref(v_b_1014_);
return v___x_1035_;
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v_b_1014_);
v_a_1048_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1025_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1025_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_1056_, lean_object* v___x_1057_, lean_object* v_as_x27_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___x_20566__boxed_1065_; lean_object* v_res_1066_; 
v___x_20566__boxed_1065_ = lean_unbox(v___x_1056_);
v_res_1066_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_20566__boxed_1065_, v___x_1057_, v_as_x27_1058_, v_b_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v_as_x27_1058_);
lean_dec_ref(v___x_1057_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = l_Lean_Level_succ___override(v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_1069_, uint8_t v___x_1070_, uint8_t v___x_1071_, uint8_t v___x_1072_, lean_object* v_val_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v_ctors_1079_, lean_object* v___x_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_value_1088_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1091_ = l_Lean_InductiveVal_numCtors(v_val_1073_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_dec_eq(v___x_1091_, v___x_1092_);
lean_dec(v___x_1091_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v___x_1080_);
lean_inc_ref(v_x_1081_);
lean_inc_ref(v___x_1074_);
v___x_1094_ = lean_array_push(v___x_1074_, v_x_1081_);
v___x_1095_ = l_Lean_Meta_mkLambdaFVars(v___x_1094_, v___x_1075_, v___x_1070_, v___x_1071_, v___x_1070_, v___x_1071_, v___x_1072_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec_ref(v___x_1094_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1076_);
v___x_1099_ = l_Lean_mkConst(v___x_1077_, v___x_1098_);
v___x_1100_ = l_Lean_mkAppN(v___x_1099_, v___x_1078_);
v___x_1101_ = l_Lean_Expr_app___override(v___x_1100_, v_a_1096_);
v___x_1102_ = l_Lean_mkAppN(v___x_1101_, v___x_1074_);
lean_dec_ref(v___x_1074_);
lean_inc_ref(v_x_1081_);
v___x_1103_ = l_Lean_Expr_app___override(v___x_1102_, v_x_1081_);
v___x_1104_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_1071_, v___x_1078_, v_ctors_1079_, v___x_1103_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v_value_1088_ = v_a_1105_;
goto v___jp_1087_;
}
else
{
lean_dec_ref(v_x_1081_);
lean_dec_ref(v_xs_1069_);
return v___x_1104_;
}
}
else
{
lean_dec_ref(v_x_1081_);
lean_dec(v___x_1077_);
lean_dec(v___x_1076_);
lean_dec_ref(v___x_1074_);
lean_dec_ref(v_xs_1069_);
return v___x_1095_;
}
}
else
{
lean_object* v___x_1106_; 
lean_dec(v___x_1077_);
lean_dec(v___x_1076_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v___x_1074_);
v___x_1106_ = l_Lean_mkRawNatLit(v___x_1080_);
v_value_1088_ = v___x_1106_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_array_push(v_xs_1069_, v_x_1081_);
v___x_1090_ = l_Lean_Meta_mkLambdaFVars(v___x_1089_, v_value_1088_, v___x_1070_, v___x_1071_, v___x_1070_, v___x_1071_, v___x_1072_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec_ref(v___x_1089_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_1107_ = _args[0];
lean_object* v___x_1108_ = _args[1];
lean_object* v___x_1109_ = _args[2];
lean_object* v___x_1110_ = _args[3];
lean_object* v_val_1111_ = _args[4];
lean_object* v___x_1112_ = _args[5];
lean_object* v___x_1113_ = _args[6];
lean_object* v___x_1114_ = _args[7];
lean_object* v___x_1115_ = _args[8];
lean_object* v___x_1116_ = _args[9];
lean_object* v_ctors_1117_ = _args[10];
lean_object* v___x_1118_ = _args[11];
lean_object* v_x_1119_ = _args[12];
lean_object* v___y_1120_ = _args[13];
lean_object* v___y_1121_ = _args[14];
lean_object* v___y_1122_ = _args[15];
lean_object* v___y_1123_ = _args[16];
lean_object* v___y_1124_ = _args[17];
_start:
{
uint8_t v___x_20657__boxed_1125_; uint8_t v___x_20658__boxed_1126_; uint8_t v___x_20659__boxed_1127_; lean_object* v_res_1128_; 
v___x_20657__boxed_1125_ = lean_unbox(v___x_1108_);
v___x_20658__boxed_1126_ = lean_unbox(v___x_1109_);
v___x_20659__boxed_1127_ = lean_unbox(v___x_1110_);
v_res_1128_ = l_Lean_mkCtorIdx___lam__0(v_xs_1107_, v___x_20657__boxed_1125_, v___x_20658__boxed_1126_, v___x_20659__boxed_1127_, v_val_1111_, v___x_1112_, v___x_1113_, v___x_1114_, v___x_1115_, v___x_1116_, v_ctors_1117_, v___x_1118_, v_x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v_ctors_1117_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_val_1111_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
v___x_1136_ = lean_apply_6(v_k_1129_, v_b_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, lean_box(0));
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1137_, v_b_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1145_, uint8_t v_bi_1146_, lean_object* v_type_1147_, lean_object* v_k_1148_, uint8_t v_kind_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1155_, 0, v_k_1148_);
v___x_1156_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1145_, v_bi_1146_, v_type_1147_, v___f_1155_, v_kind_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1156_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1156_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1173_, lean_object* v_bi_1174_, lean_object* v_type_1175_, lean_object* v_k_1176_, lean_object* v_kind_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_bi_boxed_1183_; uint8_t v_kind_boxed_1184_; lean_object* v_res_1185_; 
v_bi_boxed_1183_ = lean_unbox(v_bi_1174_);
v_kind_boxed_1184_ = lean_unbox(v_kind_1177_);
v_res_1185_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1173_, v_bi_boxed_1183_, v_type_1175_, v_k_1176_, v_kind_boxed_1184_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_1186_, lean_object* v_type_1187_, lean_object* v_k_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = 0;
v___x_1195_ = 0;
v___x_1196_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1186_, v___x_1194_, v_type_1187_, v_k_1188_, v___x_1195_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1197_, lean_object* v_type_1198_, lean_object* v_k_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1197_, v_type_1198_, v_k_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object* v_env_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v_nextMacroScope_1211_; lean_object* v_ngen_1212_; lean_object* v_auxDeclNGen_1213_; lean_object* v_traceState_1214_; lean_object* v_recordedDeps_1215_; lean_object* v_messages_1216_; lean_object* v_infoState_1217_; lean_object* v_snapshotTasks_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1244_; 
v___x_1210_ = lean_st_ref_take(v___y_1208_);
v_nextMacroScope_1211_ = lean_ctor_get(v___x_1210_, 1);
v_ngen_1212_ = lean_ctor_get(v___x_1210_, 2);
v_auxDeclNGen_1213_ = lean_ctor_get(v___x_1210_, 3);
v_traceState_1214_ = lean_ctor_get(v___x_1210_, 4);
v_recordedDeps_1215_ = lean_ctor_get(v___x_1210_, 6);
v_messages_1216_ = lean_ctor_get(v___x_1210_, 7);
v_infoState_1217_ = lean_ctor_get(v___x_1210_, 8);
v_snapshotTasks_1218_ = lean_ctor_get(v___x_1210_, 9);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; lean_object* v_unused_1246_; 
v_unused_1245_ = lean_ctor_get(v___x_1210_, 5);
lean_dec(v_unused_1245_);
v_unused_1246_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1246_);
v___x_1220_ = v___x_1210_;
v_isShared_1221_ = v_isSharedCheck_1244_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snapshotTasks_1218_);
lean_inc(v_infoState_1217_);
lean_inc(v_messages_1216_);
lean_inc(v_recordedDeps_1215_);
lean_inc(v_traceState_1214_);
lean_inc(v_auxDeclNGen_1213_);
lean_inc(v_ngen_1212_);
lean_inc(v_nextMacroScope_1211_);
lean_dec(v___x_1210_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1244_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 5, v___x_1222_);
lean_ctor_set(v___x_1220_, 0, v_env_1206_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_env_1206_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_nextMacroScope_1211_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_ngen_1212_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_auxDeclNGen_1213_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_traceState_1214_);
lean_ctor_set(v_reuseFailAlloc_1243_, 5, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1243_, 6, v_recordedDeps_1215_);
lean_ctor_set(v_reuseFailAlloc_1243_, 7, v_messages_1216_);
lean_ctor_set(v_reuseFailAlloc_1243_, 8, v_infoState_1217_);
lean_ctor_set(v_reuseFailAlloc_1243_, 9, v_snapshotTasks_1218_);
v___x_1224_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_mctx_1227_; lean_object* v_zetaDeltaFVarIds_1228_; lean_object* v_postponed_1229_; lean_object* v_diag_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1241_; 
v___x_1225_ = lean_st_ref_put(v___y_1208_, v___x_1224_);
v___x_1226_ = lean_st_ref_take(v___y_1207_);
v_mctx_1227_ = lean_ctor_get(v___x_1226_, 0);
v_zetaDeltaFVarIds_1228_ = lean_ctor_get(v___x_1226_, 2);
v_postponed_1229_ = lean_ctor_get(v___x_1226_, 3);
v_diag_1230_ = lean_ctor_get(v___x_1226_, 4);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1226_, 1);
lean_dec(v_unused_1242_);
v___x_1232_ = v___x_1226_;
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_diag_1230_);
lean_inc(v_postponed_1229_);
lean_inc(v_zetaDeltaFVarIds_1228_);
lean_inc(v_mctx_1227_);
lean_dec(v___x_1226_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1235_);
v___x_1237_ = v___x_1232_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_mctx_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_zetaDeltaFVarIds_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_postponed_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_diag_1230_);
v___x_1237_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_st_ref_put(v___y_1207_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1234_);
return v___x_1239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object* v_env_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1252_, lean_object* v_impName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v_env_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_st_ref_get(v___y_1257_);
v_env_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1259_);
v___x_1261_ = l_Lean_Compiler_setImplementedBy(v_env_1260_, v_declName_1252_, v_impName_1253_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1271_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 3);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = l_Lean_MessageData_ofFormat(v___x_1267_);
v___x_1269_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1268_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1273_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_a_1272_, v___y_1255_, v___y_1257_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1274_, lean_object* v_impName_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v_declName_1274_, v_impName_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1285_, lean_object* v___x_1286_, lean_object* v_xs_1287_, uint8_t v___x_1288_, uint8_t v___x_1289_, lean_object* v_val_1290_, lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v_ctors_1295_, lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v_levelParams_1298_, lean_object* v_indName_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
lean_inc_ref(v___x_1286_);
lean_inc_ref(v___x_1285_);
v___x_1305_ = l_Lean_mkArrow(v___x_1285_, v___x_1286_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = 1;
v___x_1308_ = lean_box(v___x_1288_);
v___x_1309_ = lean_box(v___x_1289_);
v___x_1310_ = lean_box(v___x_1307_);
lean_inc_ref(v_val_1290_);
lean_inc_ref(v_xs_1287_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1311_, 0, v_xs_1287_);
lean_closure_set(v___f_1311_, 1, v___x_1308_);
lean_closure_set(v___f_1311_, 2, v___x_1309_);
lean_closure_set(v___f_1311_, 3, v___x_1310_);
lean_closure_set(v___f_1311_, 4, v_val_1290_);
lean_closure_set(v___f_1311_, 5, v___x_1291_);
lean_closure_set(v___f_1311_, 6, v___x_1286_);
lean_closure_set(v___f_1311_, 7, v___x_1292_);
lean_closure_set(v___f_1311_, 8, v___x_1293_);
lean_closure_set(v___f_1311_, 9, v___x_1294_);
lean_closure_set(v___f_1311_, 10, v_ctors_1295_);
lean_closure_set(v___f_1311_, 11, v___x_1296_);
v___x_1312_ = l_Lean_Meta_mkForallFVars(v_xs_1287_, v_a_1306_, v___x_1288_, v___x_1289_, v___x_1289_, v___x_1307_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec_ref(v_xs_1287_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1315_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1314_, v___x_1285_, v___f_1311_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; lean_object* v_env_1318_; uint32_t v___x_1319_; lean_object* v___x_1320_; uint32_t v___x_1321_; uint32_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1466_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc_n(v_a_1316_, 2);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = lean_st_ref_get(v___y_1303_);
v_env_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_env_1318_);
lean_dec(v___x_1317_);
v___x_1319_ = l_Lean_getMaxHeight(v_env_1318_, v_a_1316_);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = 1;
v___x_1322_ = lean_uint32_add(v___x_1319_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1323_, 0, v___x_1322_);
lean_inc(v_a_1313_);
lean_inc(v_levelParams_1298_);
lean_inc(v___x_1297_);
v___x_1324_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1297_, v_levelParams_1298_, v_a_1313_, v_a_1316_, v___x_1323_, v___y_1303_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1466_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1466_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___x_1357_; 
lean_inc_ref(v___x_1330_);
v___x_1357_ = l_Lean_addDecl(v___x_1330_, v___x_1288_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1358_; lean_object* v_env_1359_; lean_object* v_nextMacroScope_1360_; lean_object* v_ngen_1361_; lean_object* v_auxDeclNGen_1362_; lean_object* v_traceState_1363_; lean_object* v_recordedDeps_1364_; lean_object* v_messages_1365_; lean_object* v_infoState_1366_; lean_object* v_snapshotTasks_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref_known(v___x_1357_, 1);
v___x_1358_ = lean_st_ref_take(v___y_1303_);
v_env_1359_ = lean_ctor_get(v___x_1358_, 0);
v_nextMacroScope_1360_ = lean_ctor_get(v___x_1358_, 1);
v_ngen_1361_ = lean_ctor_get(v___x_1358_, 2);
v_auxDeclNGen_1362_ = lean_ctor_get(v___x_1358_, 3);
v_traceState_1363_ = lean_ctor_get(v___x_1358_, 4);
v_recordedDeps_1364_ = lean_ctor_get(v___x_1358_, 6);
v_messages_1365_ = lean_ctor_get(v___x_1358_, 7);
v_infoState_1366_ = lean_ctor_get(v___x_1358_, 8);
v_snapshotTasks_1367_ = lean_ctor_get(v___x_1358_, 9);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1358_, 5);
lean_dec(v_unused_1464_);
v___x_1369_ = v___x_1358_;
v_isShared_1370_ = v_isSharedCheck_1463_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snapshotTasks_1367_);
lean_inc(v_infoState_1366_);
lean_inc(v_messages_1365_);
lean_inc(v_recordedDeps_1364_);
lean_inc(v_traceState_1363_);
lean_inc(v_auxDeclNGen_1362_);
lean_inc(v_ngen_1361_);
lean_inc(v_nextMacroScope_1360_);
lean_inc(v_env_1359_);
lean_dec(v___x_1358_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1463_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc(v___x_1297_);
v___x_1371_ = l_Lean_Meta_addToCompletionBlackList(v_env_1359_, v___x_1297_);
v___x_1372_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 5, v___x_1372_);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_nextMacroScope_1360_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_ngen_1361_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_auxDeclNGen_1362_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_traceState_1363_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1462_, 6, v_recordedDeps_1364_);
lean_ctor_set(v_reuseFailAlloc_1462_, 7, v_messages_1365_);
lean_ctor_set(v_reuseFailAlloc_1462_, 8, v_infoState_1366_);
lean_ctor_set(v_reuseFailAlloc_1462_, 9, v_snapshotTasks_1367_);
v___x_1374_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_mctx_1377_; lean_object* v_zetaDeltaFVarIds_1378_; lean_object* v_postponed_1379_; lean_object* v_diag_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1460_; 
v___x_1375_ = lean_st_ref_put(v___y_1303_, v___x_1374_);
v___x_1376_ = lean_st_ref_take(v___y_1301_);
v_mctx_1377_ = lean_ctor_get(v___x_1376_, 0);
v_zetaDeltaFVarIds_1378_ = lean_ctor_get(v___x_1376_, 2);
v_postponed_1379_ = lean_ctor_get(v___x_1376_, 3);
v_diag_1380_ = lean_ctor_get(v___x_1376_, 4);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v___x_1376_, 1);
lean_dec(v_unused_1461_);
v___x_1382_ = v___x_1376_;
v_isShared_1383_ = v_isSharedCheck_1460_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_diag_1380_);
lean_inc(v_postponed_1379_);
lean_inc(v_zetaDeltaFVarIds_1378_);
lean_inc(v_mctx_1377_);
lean_dec(v___x_1376_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1460_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_mctx_1377_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_zetaDeltaFVarIds_1378_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_postponed_1379_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_diag_1380_);
v___x_1386_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_env_1389_; lean_object* v_nextMacroScope_1390_; lean_object* v_ngen_1391_; lean_object* v_auxDeclNGen_1392_; lean_object* v_traceState_1393_; lean_object* v_recordedDeps_1394_; lean_object* v_messages_1395_; lean_object* v_infoState_1396_; lean_object* v_snapshotTasks_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1457_; 
v___x_1387_ = lean_st_ref_put(v___y_1301_, v___x_1386_);
v___x_1388_ = lean_st_ref_take(v___y_1303_);
v_env_1389_ = lean_ctor_get(v___x_1388_, 0);
v_nextMacroScope_1390_ = lean_ctor_get(v___x_1388_, 1);
v_ngen_1391_ = lean_ctor_get(v___x_1388_, 2);
v_auxDeclNGen_1392_ = lean_ctor_get(v___x_1388_, 3);
v_traceState_1393_ = lean_ctor_get(v___x_1388_, 4);
v_recordedDeps_1394_ = lean_ctor_get(v___x_1388_, 6);
v_messages_1395_ = lean_ctor_get(v___x_1388_, 7);
v_infoState_1396_ = lean_ctor_get(v___x_1388_, 8);
v_snapshotTasks_1397_ = lean_ctor_get(v___x_1388_, 9);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1388_, 5);
lean_dec(v_unused_1458_);
v___x_1399_ = v___x_1388_;
v_isShared_1400_ = v_isSharedCheck_1457_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snapshotTasks_1397_);
lean_inc(v_infoState_1396_);
lean_inc(v_messages_1395_);
lean_inc(v_recordedDeps_1394_);
lean_inc(v_traceState_1393_);
lean_inc(v_auxDeclNGen_1392_);
lean_inc(v_ngen_1391_);
lean_inc(v_nextMacroScope_1390_);
lean_inc(v_env_1389_);
lean_dec(v___x_1388_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1457_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_inc(v___x_1297_);
v___x_1401_ = l_Lean_addProtected(v_env_1389_, v___x_1297_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 5, v___x_1372_);
lean_ctor_set(v___x_1399_, 0, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_nextMacroScope_1390_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_ngen_1391_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_auxDeclNGen_1392_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_traceState_1393_);
lean_ctor_set(v_reuseFailAlloc_1456_, 5, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1456_, 6, v_recordedDeps_1394_);
lean_ctor_set(v_reuseFailAlloc_1456_, 7, v_messages_1395_);
lean_ctor_set(v_reuseFailAlloc_1456_, 8, v_infoState_1396_);
lean_ctor_set(v_reuseFailAlloc_1456_, 9, v_snapshotTasks_1397_);
v___x_1403_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_mctx_1406_; lean_object* v_zetaDeltaFVarIds_1407_; lean_object* v_postponed_1408_; lean_object* v_diag_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1454_; 
v___x_1404_ = lean_st_ref_put(v___y_1303_, v___x_1403_);
v___x_1405_ = lean_st_ref_take(v___y_1301_);
v_mctx_1406_ = lean_ctor_get(v___x_1405_, 0);
v_zetaDeltaFVarIds_1407_ = lean_ctor_get(v___x_1405_, 2);
v_postponed_1408_ = lean_ctor_get(v___x_1405_, 3);
v_diag_1409_ = lean_ctor_get(v___x_1405_, 4);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1405_, 1);
lean_dec(v_unused_1455_);
v___x_1411_ = v___x_1405_;
v_isShared_1412_ = v_isSharedCheck_1454_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_diag_1409_);
lean_inc(v_postponed_1408_);
lean_inc(v_zetaDeltaFVarIds_1407_);
lean_inc(v_mctx_1406_);
lean_dec(v___x_1405_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1454_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v___x_1384_);
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_mctx_1406_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_zetaDeltaFVarIds_1407_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_postponed_1408_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_diag_1409_);
v___x_1414_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_env_1417_; uint8_t v___x_1418_; 
v___x_1415_ = lean_st_ref_put(v___y_1301_, v___x_1414_);
v___x_1416_ = lean_st_ref_get(v___y_1303_);
v_env_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_env_1417_);
lean_dec(v___x_1416_);
lean_inc(v_indName_1299_);
v___x_1418_ = l_Lean_isMarkedMeta(v_env_1417_, v_indName_1299_);
if (v___x_1418_ == 0)
{
v___y_1337_ = v___y_1300_;
v___y_1338_ = v___y_1301_;
v___y_1339_ = v___y_1302_;
v___y_1340_ = v___y_1303_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1419_; lean_object* v_env_1420_; lean_object* v_nextMacroScope_1421_; lean_object* v_ngen_1422_; lean_object* v_auxDeclNGen_1423_; lean_object* v_traceState_1424_; lean_object* v_recordedDeps_1425_; lean_object* v_messages_1426_; lean_object* v_infoState_1427_; lean_object* v_snapshotTasks_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1451_; 
v___x_1419_ = lean_st_ref_take(v___y_1303_);
v_env_1420_ = lean_ctor_get(v___x_1419_, 0);
v_nextMacroScope_1421_ = lean_ctor_get(v___x_1419_, 1);
v_ngen_1422_ = lean_ctor_get(v___x_1419_, 2);
v_auxDeclNGen_1423_ = lean_ctor_get(v___x_1419_, 3);
v_traceState_1424_ = lean_ctor_get(v___x_1419_, 4);
v_recordedDeps_1425_ = lean_ctor_get(v___x_1419_, 6);
v_messages_1426_ = lean_ctor_get(v___x_1419_, 7);
v_infoState_1427_ = lean_ctor_get(v___x_1419_, 8);
v_snapshotTasks_1428_ = lean_ctor_get(v___x_1419_, 9);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1419_, 5);
lean_dec(v_unused_1452_);
v___x_1430_ = v___x_1419_;
v_isShared_1431_ = v_isSharedCheck_1451_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snapshotTasks_1428_);
lean_inc(v_infoState_1427_);
lean_inc(v_messages_1426_);
lean_inc(v_recordedDeps_1425_);
lean_inc(v_traceState_1424_);
lean_inc(v_auxDeclNGen_1423_);
lean_inc(v_ngen_1422_);
lean_inc(v_nextMacroScope_1421_);
lean_inc(v_env_1420_);
lean_dec(v___x_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1451_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_inc(v___x_1297_);
v___x_1432_ = l_Lean_markMeta(v_env_1420_, v___x_1297_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 5, v___x_1372_);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_nextMacroScope_1421_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_ngen_1422_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_auxDeclNGen_1423_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_traceState_1424_);
lean_ctor_set(v_reuseFailAlloc_1450_, 5, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1450_, 6, v_recordedDeps_1425_);
lean_ctor_set(v_reuseFailAlloc_1450_, 7, v_messages_1426_);
lean_ctor_set(v_reuseFailAlloc_1450_, 8, v_infoState_1427_);
lean_ctor_set(v_reuseFailAlloc_1450_, 9, v_snapshotTasks_1428_);
v___x_1434_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_mctx_1437_; lean_object* v_zetaDeltaFVarIds_1438_; lean_object* v_postponed_1439_; lean_object* v_diag_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v___x_1435_ = lean_st_ref_put(v___y_1303_, v___x_1434_);
v___x_1436_ = lean_st_ref_take(v___y_1301_);
v_mctx_1437_ = lean_ctor_get(v___x_1436_, 0);
v_zetaDeltaFVarIds_1438_ = lean_ctor_get(v___x_1436_, 2);
v_postponed_1439_ = lean_ctor_get(v___x_1436_, 3);
v_diag_1440_ = lean_ctor_get(v___x_1436_, 4);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1436_, 1);
lean_dec(v_unused_1449_);
v___x_1442_ = v___x_1436_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_diag_1440_);
lean_inc(v_postponed_1439_);
lean_inc(v_zetaDeltaFVarIds_1438_);
lean_inc(v_mctx_1437_);
lean_dec(v___x_1436_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1384_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_mctx_1437_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_zetaDeltaFVarIds_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_postponed_1439_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_diag_1440_);
v___x_1445_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_st_ref_put(v___y_1301_, v___x_1445_);
v___y_1337_ = v___y_1300_;
v___y_1338_ = v___y_1301_;
v___y_1339_ = v___y_1302_;
v___y_1340_ = v___y_1303_;
goto v___jp_1336_;
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
}
}
}
}
else
{
lean_dec_ref(v___x_1330_);
lean_dec(v_a_1313_);
lean_dec(v_indName_1299_);
lean_dec(v_levelParams_1298_);
lean_dec(v___x_1297_);
lean_dec_ref(v_val_1290_);
return v___x_1357_;
}
v___jp_1331_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_compileDecl(v___x_1330_, v___x_1289_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref_known(v___x_1334_, 1);
v___x_1335_ = l_Lean_enableRealizationsForConst(v___x_1297_, v___y_1332_, v___y_1333_);
return v___x_1335_;
}
else
{
lean_dec(v___x_1297_);
return v___x_1334_;
}
}
v___jp_1336_:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = l_Lean_InductiveVal_numCtors(v_val_1290_);
lean_dec_ref(v_val_1290_);
v___x_1342_ = lean_nat_dec_eq(v___x_1341_, v___x_1320_);
lean_dec(v___x_1341_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_indName_1299_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_1299_, v_levelParams_1298_, v_a_1313_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
lean_inc(v___x_1297_);
v___x_1346_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v___x_1297_, v_a_1345_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_dec_ref_known(v___x_1346_, 1);
v___y_1332_ = v___y_1339_;
v___y_1333_ = v___y_1340_;
goto v___jp_1331_;
}
else
{
lean_dec_ref(v___x_1330_);
lean_dec(v___x_1297_);
return v___x_1346_;
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref(v___x_1330_);
lean_dec(v___x_1297_);
v_a_1347_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1344_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_dec(v_a_1313_);
lean_dec(v_indName_1299_);
lean_dec(v_levelParams_1298_);
v___y_1332_ = v___y_1339_;
v___y_1333_ = v___y_1340_;
goto v___jp_1331_;
}
}
else
{
uint8_t v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_a_1313_);
lean_dec(v_indName_1299_);
lean_dec(v_levelParams_1298_);
v___x_1355_ = 2;
lean_inc(v___x_1297_);
v___x_1356_ = l_Lean_Meta_setInlineAttribute(v___x_1297_, v___x_1355_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
v___y_1332_ = v___y_1339_;
v___y_1333_ = v___y_1340_;
goto v___jp_1331_;
}
else
{
lean_dec_ref(v___x_1330_);
lean_dec(v___x_1297_);
return v___x_1356_;
}
}
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1313_);
lean_dec(v_indName_1299_);
lean_dec(v_levelParams_1298_);
lean_dec(v___x_1297_);
lean_dec_ref(v_val_1290_);
v_a_1467_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1315_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1315_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___f_1311_);
lean_dec(v_indName_1299_);
lean_dec(v_levelParams_1298_);
lean_dec(v___x_1297_);
lean_dec_ref(v_val_1290_);
lean_dec_ref(v___x_1285_);
v_a_1475_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1312_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1312_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_indName_1299_);
lean_dec(v_levelParams_1298_);
lean_dec(v___x_1297_);
lean_dec(v___x_1296_);
lean_dec(v_ctors_1295_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1293_);
lean_dec(v___x_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v_val_1290_);
lean_dec_ref(v_xs_1287_);
lean_dec_ref(v___x_1286_);
lean_dec_ref(v___x_1285_);
v_a_1483_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1305_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1305_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1491_ = _args[0];
lean_object* v___x_1492_ = _args[1];
lean_object* v_xs_1493_ = _args[2];
lean_object* v___x_1494_ = _args[3];
lean_object* v___x_1495_ = _args[4];
lean_object* v_val_1496_ = _args[5];
lean_object* v___x_1497_ = _args[6];
lean_object* v___x_1498_ = _args[7];
lean_object* v___x_1499_ = _args[8];
lean_object* v___x_1500_ = _args[9];
lean_object* v_ctors_1501_ = _args[10];
lean_object* v___x_1502_ = _args[11];
lean_object* v___x_1503_ = _args[12];
lean_object* v_levelParams_1504_ = _args[13];
lean_object* v_indName_1505_ = _args[14];
lean_object* v___y_1506_ = _args[15];
lean_object* v___y_1507_ = _args[16];
lean_object* v___y_1508_ = _args[17];
lean_object* v___y_1509_ = _args[18];
lean_object* v___y_1510_ = _args[19];
_start:
{
uint8_t v___x_20971__boxed_1511_; uint8_t v___x_20972__boxed_1512_; lean_object* v_res_1513_; 
v___x_20971__boxed_1511_ = lean_unbox(v___x_1494_);
v___x_20972__boxed_1512_ = lean_unbox(v___x_1495_);
v_res_1513_ = l_Lean_mkCtorIdx___lam__1(v___x_1491_, v___x_1492_, v_xs_1493_, v___x_20971__boxed_1511_, v___x_20972__boxed_1512_, v_val_1496_, v___x_1497_, v___x_1498_, v___x_1499_, v___x_1500_, v_ctors_1501_, v___x_1502_, v___x_1503_, v_levelParams_1504_, v_indName_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_bs_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_lt(v_i_1515_, v_sz_1514_);
if (v___x_1517_ == 0)
{
return v_bs_1516_;
}
else
{
lean_object* v_v_1518_; lean_object* v___x_1519_; lean_object* v_bs_x27_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v_v_1518_ = lean_array_uget(v_bs_1516_, v_i_1515_);
v___x_1519_ = lean_unsigned_to_nat(0u);
v_bs_x27_1520_ = lean_array_uset(v_bs_1516_, v_i_1515_, v___x_1519_);
v___x_1521_ = l_Lean_Expr_fvarId_x21(v_v_1518_);
lean_dec(v_v_1518_);
v___x_1522_ = 1;
v___x_1523_ = lean_box(v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1521_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = ((size_t)1ULL);
v___x_1526_ = lean_usize_add(v_i_1515_, v___x_1525_);
v___x_1527_ = lean_array_uset(v_bs_x27_1520_, v_i_1515_, v___x_1524_);
v_i_1515_ = v___x_1526_;
v_bs_1516_ = v___x_1527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_bs_1531_){
_start:
{
size_t v_sz_boxed_1532_; size_t v_i_boxed_1533_; lean_object* v_res_1534_; 
v_sz_boxed_1532_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1533_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_boxed_1532_, v_i_boxed_1533_, v_bs_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object* v_bs_1535_, lean_object* v_k_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1535_, v_k_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_a_1551_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1542_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1542_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object* v_bs_1559_, lean_object* v_k_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_1559_, v_k_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_bs_1559_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object* v_bs_1567_, lean_object* v_k_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_sz_1574_ = lean_array_size(v_bs_1567_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_1574_, v___x_1575_, v_bs_1567_);
v___x_1577_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v___x_1576_, v_k_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object* v_bs_1578_, lean_object* v_k_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_1578_, v_k_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1589_, lean_object* v_indName_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, uint8_t v___x_1593_, uint8_t v___x_1594_, lean_object* v_val_1595_, lean_object* v___x_1596_, lean_object* v_ctors_1597_, lean_object* v___x_1598_, lean_object* v_levelParams_1599_, lean_object* v_xs_1600_, lean_object* v_x_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1589_);
lean_inc_ref_n(v_xs_1600_, 3);
v___x_1608_ = l_Array_toSubarray___redArg(v_xs_1600_, v___x_1607_, v_numParams_1589_);
v___x_1609_ = l_Subarray_copy___redArg(v___x_1608_);
v___x_1610_ = lean_array_get_size(v_xs_1600_);
v___x_1611_ = l_Array_toSubarray___redArg(v_xs_1600_, v_numParams_1589_, v___x_1610_);
v___x_1612_ = l_Subarray_copy___redArg(v___x_1611_);
lean_inc(v___x_1591_);
lean_inc(v_indName_1590_);
v___x_1613_ = l_Lean_mkConst(v_indName_1590_, v___x_1591_);
v___x_1614_ = l_Lean_mkAppN(v___x_1613_, v_xs_1600_);
v___x_1615_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1616_ = l_Lean_mkConst(v___x_1615_, v___x_1592_);
v___x_1617_ = lean_box(v___x_1593_);
v___x_1618_ = lean_box(v___x_1594_);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1619_, 0, v___x_1614_);
lean_closure_set(v___f_1619_, 1, v___x_1616_);
lean_closure_set(v___f_1619_, 2, v_xs_1600_);
lean_closure_set(v___f_1619_, 3, v___x_1617_);
lean_closure_set(v___f_1619_, 4, v___x_1618_);
lean_closure_set(v___f_1619_, 5, v_val_1595_);
lean_closure_set(v___f_1619_, 6, v___x_1612_);
lean_closure_set(v___f_1619_, 7, v___x_1591_);
lean_closure_set(v___f_1619_, 8, v___x_1596_);
lean_closure_set(v___f_1619_, 9, v___x_1609_);
lean_closure_set(v___f_1619_, 10, v_ctors_1597_);
lean_closure_set(v___f_1619_, 11, v___x_1607_);
lean_closure_set(v___f_1619_, 12, v___x_1598_);
lean_closure_set(v___f_1619_, 13, v_levelParams_1599_);
lean_closure_set(v___f_1619_, 14, v_indName_1590_);
v___x_1620_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_xs_1600_, v___f_1619_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1621_ = _args[0];
lean_object* v_indName_1622_ = _args[1];
lean_object* v___x_1623_ = _args[2];
lean_object* v___x_1624_ = _args[3];
lean_object* v___x_1625_ = _args[4];
lean_object* v___x_1626_ = _args[5];
lean_object* v_val_1627_ = _args[6];
lean_object* v___x_1628_ = _args[7];
lean_object* v_ctors_1629_ = _args[8];
lean_object* v___x_1630_ = _args[9];
lean_object* v_levelParams_1631_ = _args[10];
lean_object* v_xs_1632_ = _args[11];
lean_object* v_x_1633_ = _args[12];
lean_object* v___y_1634_ = _args[13];
lean_object* v___y_1635_ = _args[14];
lean_object* v___y_1636_ = _args[15];
lean_object* v___y_1637_ = _args[16];
lean_object* v___y_1638_ = _args[17];
_start:
{
uint8_t v___x_21417__boxed_1639_; uint8_t v___x_21418__boxed_1640_; lean_object* v_res_1641_; 
v___x_21417__boxed_1639_ = lean_unbox(v___x_1625_);
v___x_21418__boxed_1640_ = lean_unbox(v___x_1626_);
v_res_1641_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1621_, v_indName_1622_, v___x_1623_, v___x_1624_, v___x_21417__boxed_1639_, v___x_21418__boxed_1640_, v_val_1627_, v___x_1628_, v_ctors_1629_, v___x_1630_, v_levelParams_1631_, v_xs_1632_, v_x_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec_ref(v_x_1633_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
if (lean_obj_tag(v_a_1642_) == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = l_List_reverse___redArg(v_a_1643_);
return v___x_1644_;
}
else
{
lean_object* v_head_1645_; lean_object* v_tail_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1655_; 
v_head_1645_ = lean_ctor_get(v_a_1642_, 0);
v_tail_1646_ = lean_ctor_get(v_a_1642_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1648_ = v_a_1642_;
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_tail_1646_);
lean_inc(v_head_1645_);
lean_dec(v_a_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_mkLevelParam(v_head_1645_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v_a_1643_);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_a_1643_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v_a_1642_ = v_tail_1646_;
v_a_1643_ = v___x_1652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(lean_object* v_ref_1656_, lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_toCold_1663_; lean_object* v_currRecDepth_1664_; lean_object* v_ref_1665_; uint16_t v_optionFlags_1666_; uint8_t v_suppressElabErrors_1667_; uint8_t v_isRecordingDeps_1668_; lean_object* v_ref_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_toCold_1663_ = lean_ctor_get(v___y_1660_, 0);
v_currRecDepth_1664_ = lean_ctor_get(v___y_1660_, 1);
v_ref_1665_ = lean_ctor_get(v___y_1660_, 2);
v_optionFlags_1666_ = lean_ctor_get_uint16(v___y_1660_, sizeof(void*)*3);
v_suppressElabErrors_1667_ = lean_ctor_get_uint8(v___y_1660_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1668_ = lean_ctor_get_uint8(v___y_1660_, sizeof(void*)*3 + 3);
v_ref_1669_ = l_Lean_replaceRef(v_ref_1656_, v_ref_1665_);
lean_inc(v_currRecDepth_1664_);
lean_inc_ref(v_toCold_1663_);
v___x_1670_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1670_, 0, v_toCold_1663_);
lean_ctor_set(v___x_1670_, 1, v_currRecDepth_1664_);
lean_ctor_set(v___x_1670_, 2, v_ref_1669_);
lean_ctor_set_uint16(v___x_1670_, sizeof(void*)*3, v_optionFlags_1666_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 2, v_suppressElabErrors_1667_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 3, v_isRecordingDeps_1668_);
v___x_1671_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1657_, v___y_1658_, v___y_1659_, v___x_1670_, v___y_1661_);
lean_dec_ref_known(v___x_1670_, 3);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1672_, lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1672_, v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v_ref_1672_);
return v_res_1679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1682_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
lean_ctor_set(v___x_1685_, 2, v___x_1684_);
lean_ctor_set(v___x_1685_, 3, v___x_1684_);
lean_ctor_set(v___x_1685_, 4, v___x_1683_);
lean_ctor_set(v___x_1685_, 5, v___x_1683_);
lean_ctor_set(v___x_1685_, 6, v___x_1683_);
lean_ctor_set(v___x_1685_, 7, v___x_1683_);
lean_ctor_set(v___x_1685_, 8, v___x_1683_);
lean_ctor_set(v___x_1685_, 9, v___x_1683_);
lean_ctor_set(v___x_1685_, 10, v___x_1683_);
lean_ctor_set(v___x_1685_, 11, v___x_1682_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_unsigned_to_nat(32u);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3(void){
_start:
{
size_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1689_ = ((size_t)5ULL);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_unsigned_to_nat(32u);
v___x_1692_ = lean_mk_empty_array_with_capacity(v___x_1691_);
v___x_1693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2);
v___x_1694_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1692_);
lean_ctor_set(v___x_1694_, 2, v___x_1690_);
lean_ctor_set(v___x_1694_, 3, v___x_1690_);
lean_ctor_set_usize(v___x_1694_, 4, v___x_1689_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1695_ = lean_box(1);
v___x_1696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3);
v___x_1697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___x_1696_);
lean_ctor_set(v___x_1698_, 2, v___x_1695_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7));
v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9));
v___x_1707_ = l_Lean_stringToMessageData(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(lean_object* v_msg_1720_, lean_object* v_declHint_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_env_1726_; uint8_t v___x_1727_; 
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_st_ref_get(v___y_1722_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_ref(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1727_ = l_Lean_Name_isAnonymous(v_declHint_1721_);
if (v___x_1727_ == 0)
{
uint8_t v_isExporting_1728_; 
v_isExporting_1728_ = lean_ctor_get_uint8(v_env_1726_, sizeof(void*)*13);
if (v_isExporting_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v_env_1726_);
lean_dec(v_declHint_1721_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_msg_1720_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
lean_inc_ref(v_env_1726_);
v___x_1730_ = l_Lean_Environment_setExporting(v_env_1726_, v___x_1727_);
lean_inc(v_declHint_1721_);
lean_inc_ref(v___x_1730_);
v___x_1731_ = l_Lean_Environment_contains(v___x_1730_, v_declHint_1721_, v_isExporting_1728_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_env_1726_);
lean_dec(v_declHint_1721_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_msg_1720_);
return v___x_1732_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_c_1738_; lean_object* v___x_1739_; 
v___x_1733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1);
v___x_1734_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4);
v___x_1735_ = l_Lean_Options_empty;
v___x_1736_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1730_);
lean_ctor_set(v___x_1736_, 1, v___x_1733_);
lean_ctor_set(v___x_1736_, 2, v___x_1734_);
lean_ctor_set(v___x_1736_, 3, v___x_1735_);
lean_inc(v_declHint_1721_);
v___x_1737_ = l_Lean_MessageData_ofConstName(v_declHint_1721_, v___x_1727_);
v_c_1738_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1738_, 0, v___x_1736_);
lean_ctor_set(v_c_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1726_, v_declHint_1721_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec_ref(v_env_1726_);
lean_dec(v_declHint_1721_);
v___x_1740_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v_c_1738_);
v___x_1742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_MessageData_note(v___x_1743_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_msg_1720_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
else
{
lean_object* v_val_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1781_; 
v_val_1747_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1749_ = v___x_1739_;
v_isShared_1750_ = v_isSharedCheck_1781_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_val_1747_);
lean_dec(v___x_1739_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1781_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v_moduleNames_1752_; lean_object* v_mod_1753_; uint8_t v___x_1754_; 
v___x_1751_ = l_Lean_Environment_header(v_env_1726_);
lean_dec_ref(v_env_1726_);
v_moduleNames_1752_ = lean_ctor_get(v___x_1751_, 4);
lean_inc_ref(v_moduleNames_1752_);
lean_dec_ref(v___x_1751_);
v_mod_1753_ = lean_array_get(v___x_1724_, v_moduleNames_1752_, v_val_1747_);
lean_dec(v_val_1747_);
lean_dec_ref(v_moduleNames_1752_);
v___x_1754_ = l_Lean_isPrivateName(v_declHint_1721_);
lean_dec(v_declHint_1721_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_c_1738_);
v___x_1757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_MessageData_ofName(v_mod_1753_);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_MessageData_note(v___x_1762_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v_msg_1720_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1764_);
v___x_1766_ = v___x_1749_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v_c_1738_);
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = l_Lean_MessageData_ofName(v_mod_1753_);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_MessageData_note(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_msg_1720_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1777_);
v___x_1779_ = v___x_1749_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1782_; 
lean_dec_ref(v_env_1726_);
lean_dec(v_declHint_1721_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_msg_1720_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___boxed(lean_object* v_msg_1783_, lean_object* v_declHint_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1783_, v_declHint_1784_, v___y_1785_);
lean_dec(v___y_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(lean_object* v_msg_1788_, lean_object* v_declHint_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1805_; 
v___x_1795_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1788_, v_declHint_1789_, v___y_1793_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1805_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1805_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = l_Lean_unknownIdentifierMessageTag;
v___x_1801_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_a_1796_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22___boxed(lean_object* v_msg_1806_, lean_object* v_declHint_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1806_, v_declHint_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(lean_object* v_ref_1814_, lean_object* v_msg_1815_, lean_object* v_declHint_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v_a_1823_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1815_, v_declHint_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1814_, v_a_1823_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg___boxed(lean_object* v_ref_1825_, lean_object* v_msg_1826_, lean_object* v_declHint_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1825_, v_msg_1826_, v_declHint_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v_ref_1825_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1837_, lean_object* v_constName_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1844_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1845_ = 0;
lean_inc(v_constName_1838_);
v___x_1846_ = l_Lean_MessageData_ofConstName(v_constName_1838_, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1844_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1837_, v___x_1849_, v_constName_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1851_, lean_object* v_constName_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1851_, v_constName_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v_ref_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_ref_1865_; lean_object* v___x_1866_; 
v_ref_1865_ = lean_ctor_get(v___y_1862_, 2);
v___x_1866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1865_, v_constName_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v_env_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1880_ = lean_st_ref_get(v___y_1878_);
v_env_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc_ref(v_env_1881_);
lean_dec(v___x_1880_);
v___x_1882_ = 0;
lean_inc(v_constName_1874_);
v___x_1883_ = l_Lean_Environment_find_x3f(v_env_1881_, v_constName_1874_, v___x_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1884_;
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_constName_1874_);
v_val_1885_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_val_1885_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 0);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1902_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1903_ = lean_unsigned_to_nat(62u);
v___x_1904_ = lean_unsigned_to_nat(83u);
v___x_1905_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1906_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1907_ = l_mkPanicMessageWithDecl(v___x_1906_, v___x_1905_, v___x_1904_, v___x_1903_, v___x_1902_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1908_, uint8_t v___x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1912_);
v___x_1916_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1917_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v___x_1915_, v___x_1916_);
lean_dec_ref(v___x_1915_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec(v_indName_1908_);
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_2006_; 
lean_inc(v_indName_1908_);
v___x_1920_ = l_Lean_mkCtorIdxName(v_indName_1908_);
lean_inc(v___x_1920_);
v___x_1921_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1920_, v___x_1917_, v___y_1913_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_2006_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_2006_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_unbox(v_a_1922_);
lean_dec(v_a_1922_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_del_object(v___x_1924_);
lean_inc(v_indName_1908_);
v___x_1927_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1908_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
if (lean_obj_tag(v_a_1928_) == 5)
{
lean_object* v_val_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1991_; 
v_val_1929_ = lean_ctor_get(v_a_1928_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1928_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1931_ = v_a_1928_;
v_isShared_1932_ = v_isSharedCheck_1991_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_val_1929_);
lean_dec(v_a_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1991_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_toConstantVal_1933_; lean_object* v_numParams_1934_; lean_object* v_numIndices_1935_; lean_object* v_ctors_1936_; lean_object* v_levelParams_1937_; lean_object* v_type_1938_; lean_object* v___x_1939_; 
v_toConstantVal_1933_ = lean_ctor_get(v_val_1929_, 0);
v_numParams_1934_ = lean_ctor_get(v_val_1929_, 1);
lean_inc(v_numParams_1934_);
v_numIndices_1935_ = lean_ctor_get(v_val_1929_, 2);
lean_inc(v_numIndices_1935_);
v_ctors_1936_ = lean_ctor_get(v_val_1929_, 4);
lean_inc(v_ctors_1936_);
v_levelParams_1937_ = lean_ctor_get(v_toConstantVal_1933_, 1);
lean_inc(v_levelParams_1937_);
v_type_1938_ = lean_ctor_get(v_toConstantVal_1933_, 2);
lean_inc_ref_n(v_type_1938_, 2);
v___x_1939_ = l_Lean_Meta_isPropFormerType(v_type_1938_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1982_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1982_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1982_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_del_object(v___x_1942_);
lean_inc(v_indName_1908_);
v___x_1945_ = l_Lean_mkCasesOnName(v_indName_1908_);
lean_inc(v___x_1945_);
v___x_1946_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_1945_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1969_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1969_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1969_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1951_ = l_List_lengthTR___redArg(v_levelParams_1937_);
v___x_1952_ = l_Lean_ConstantInfo_levelParams(v_a_1947_);
lean_dec(v_a_1947_);
v___x_1953_ = l_List_lengthTR___redArg(v___x_1952_);
lean_dec(v___x_1952_);
v___x_1954_ = lean_nat_dec_lt(v___x_1951_, v___x_1953_);
lean_dec(v___x_1953_);
lean_dec(v___x_1951_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_dec(v___x_1945_);
lean_dec_ref(v_type_1938_);
lean_dec(v_levelParams_1937_);
lean_dec(v_ctors_1936_);
lean_dec(v_numIndices_1935_);
lean_dec(v_numParams_1934_);
lean_del_object(v___x_1931_);
lean_dec_ref(v_val_1929_);
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v___x_1955_ = lean_box(0);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1955_);
v___x_1957_ = v___x_1949_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
lean_del_object(v___x_1949_);
v___x_1959_ = lean_box(0);
lean_inc(v_levelParams_1937_);
v___x_1960_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1937_, v___x_1959_);
v___x_1961_ = lean_box(v___x_1909_);
v___x_1962_ = lean_box(v___x_1917_);
lean_inc(v_numParams_1934_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1963_, 0, v_numParams_1934_);
lean_closure_set(v___f_1963_, 1, v_indName_1908_);
lean_closure_set(v___f_1963_, 2, v___x_1960_);
lean_closure_set(v___f_1963_, 3, v___x_1959_);
lean_closure_set(v___f_1963_, 4, v___x_1961_);
lean_closure_set(v___f_1963_, 5, v___x_1962_);
lean_closure_set(v___f_1963_, 6, v_val_1929_);
lean_closure_set(v___f_1963_, 7, v___x_1945_);
lean_closure_set(v___f_1963_, 8, v_ctors_1936_);
lean_closure_set(v___f_1963_, 9, v___x_1920_);
lean_closure_set(v___f_1963_, 10, v_levelParams_1937_);
v___x_1964_ = lean_nat_add(v_numParams_1934_, v_numIndices_1935_);
lean_dec(v_numIndices_1935_);
lean_dec(v_numParams_1934_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 0, v___x_1964_);
v___x_1966_ = v___x_1931_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1938_, v___x_1966_, v___f_1963_, v___x_1909_, v___x_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v___x_1945_);
lean_dec_ref(v_type_1938_);
lean_dec(v_levelParams_1937_);
lean_dec(v_ctors_1936_);
lean_dec(v_numIndices_1935_);
lean_dec(v_numParams_1934_);
lean_del_object(v___x_1931_);
lean_dec_ref(v_val_1929_);
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v_a_1970_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1946_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1946_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec_ref(v_type_1938_);
lean_dec(v_levelParams_1937_);
lean_dec(v_ctors_1936_);
lean_dec(v_numIndices_1935_);
lean_dec(v_numParams_1934_);
lean_del_object(v___x_1931_);
lean_dec_ref(v_val_1929_);
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v___x_1978_ = lean_box(0);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1978_);
v___x_1980_ = v___x_1942_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v_type_1938_);
lean_dec(v_levelParams_1937_);
lean_dec(v_ctors_1936_);
lean_dec(v_numIndices_1935_);
lean_dec(v_numParams_1934_);
lean_del_object(v___x_1931_);
lean_dec_ref(v_val_1929_);
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v_a_1983_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1939_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1939_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec(v_a_1928_);
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v___x_1992_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_1993_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v___x_1992_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1993_;
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v_a_1994_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1927_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1927_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
lean_dec(v___x_1920_);
lean_dec(v_indName_1908_);
v___x_2002_ = lean_box(0);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_2002_);
v___x_2004_ = v___x_1924_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2007_, lean_object* v___x_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v___x_21964__boxed_2014_; lean_object* v_res_2015_; 
v___x_21964__boxed_2014_ = lean_unbox(v___x_2008_);
v_res_2015_ = l_Lean_mkCtorIdx___lam__3(v_indName_2007_, v___x_21964__boxed_2014_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2016_, lean_object* v_e_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = l_Lean_indentD(v_e_2017_);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2016_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2020_, lean_object* v___f_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2020_, v___f_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2027_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2027_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2044_, lean_object* v___f_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_mkCtorIdx___lam__5(v___f_2044_, v___f_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2051_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; uint8_t v___x_2074_; 
v___x_2064_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2065_ = 0;
v___x_2066_ = lean_box(v___x_2065_);
lean_inc_n(v_indName_2058_, 2);
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2067_, 0, v_indName_2058_);
lean_closure_set(v___f_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_MessageData_ofConstName(v_indName_2058_, v___x_2065_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2064_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2072_, 0, v___x_2071_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2073_, 0, v___f_2067_);
lean_closure_set(v___f_2073_, 1, v___f_2072_);
v___x_2074_ = l_Lean_isPrivateName(v_indName_2058_);
lean_dec(v_indName_2058_);
if (v___x_2074_ == 0)
{
uint8_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = 1;
v___x_2076_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2073_, v___x_2075_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2073_, v___x_2065_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_mkCtorIdx(v_indName_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2085_, lean_object* v___x_2086_, lean_object* v_as_2087_, lean_object* v_as_x27_2088_, lean_object* v_b_2089_, lean_object* v_a_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2085_, v___x_2086_, v_as_x27_2088_, v_b_2089_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v_as_2099_, lean_object* v_as_x27_2100_, lean_object* v_b_2101_, lean_object* v_a_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_22273__boxed_2108_; lean_object* v_res_2109_; 
v___x_22273__boxed_2108_ = lean_unbox(v___x_2097_);
v_res_2109_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_22273__boxed_2108_, v___x_2098_, v_as_2099_, v_as_x27_2100_, v_b_2101_, v_a_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v_as_x27_2100_);
lean_dec(v_as_2099_);
lean_dec_ref(v___x_2098_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2110_, lean_object* v_name_2111_, uint8_t v_bi_2112_, lean_object* v_type_2113_, lean_object* v_k_2114_, uint8_t v_kind_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2111_, v_bi_2112_, v_type_2113_, v_k_2114_, v_kind_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2122_, lean_object* v_name_2123_, lean_object* v_bi_2124_, lean_object* v_type_2125_, lean_object* v_k_2126_, lean_object* v_kind_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v_bi_boxed_2133_; uint8_t v_kind_boxed_2134_; lean_object* v_res_2135_; 
v_bi_boxed_2133_ = lean_unbox(v_bi_2124_);
v_kind_boxed_2134_ = lean_unbox(v_kind_2127_);
v_res_2135_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2122_, v_name_2123_, v_bi_boxed_2133_, v_type_2125_, v_k_2126_, v_kind_boxed_2134_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2136_, lean_object* v_name_2137_, lean_object* v_type_2138_, lean_object* v_k_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2137_, v_type_2138_, v_k_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_name_2147_, lean_object* v_type_2148_, lean_object* v_k_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2146_, v_name_2147_, v_type_2148_, v_k_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object* v_env_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_2156_, v___y_2158_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_env_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(v_env_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object* v_00_u03b1_2170_, lean_object* v_bs_2171_, lean_object* v_k_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_2171_, v_k_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_bs_2180_, lean_object* v_k_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(v_00_u03b1_2179_, v_bs_2180_, v_k_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v_bs_2180_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object* v_00_u03b1_2188_, lean_object* v_bs_2189_, lean_object* v_k_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_2189_, v_k_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_bs_2198_, lean_object* v_k_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(v_00_u03b1_2197_, v_bs_2198_, v_k_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2206_, lean_object* v_constName_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2214_, lean_object* v_constName_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2214_, v_constName_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2222_, lean_object* v_msg_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2230_, lean_object* v_msg_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2230_, v_msg_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2238_, lean_object* v_ref_2239_, lean_object* v_constName_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2239_, v_constName_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2247_, lean_object* v_ref_2248_, lean_object* v_constName_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2247_, v_ref_2248_, v_constName_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v_ref_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_object* v_00_u03b1_2256_, lean_object* v_ref_2257_, lean_object* v_msg_2258_, lean_object* v_declHint_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_2257_, v_msg_2258_, v_declHint_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_ref_2267_, lean_object* v_msg_2268_, lean_object* v_declHint_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(v_00_u03b1_2266_, v_ref_2267_, v_msg_2268_, v_declHint_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v_ref_2267_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(lean_object* v_msg_2276_, lean_object* v_declHint_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_2276_, v_declHint_2277_, v___y_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___boxed(lean_object* v_msg_2284_, lean_object* v_declHint_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(v_msg_2284_, v_declHint_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_object* v_00_u03b1_2292_, lean_object* v_ref_2293_, lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_2293_, v_msg_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___boxed(lean_object* v_00_u03b1_2301_, lean_object* v_ref_2302_, lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(v_00_u03b1_2301_, v_ref_2302_, v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v_ref_2302_);
return v_res_2309_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
