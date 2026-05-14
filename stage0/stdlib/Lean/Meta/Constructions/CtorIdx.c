// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Linter.Deprecated
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 119, 104, 54, 230, 159, 208, 234)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 246, 214, 203, 234, 6, 143, 204)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(134, 216, 207, 23, 24, 47, 82, 122)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
static const lean_string_object l_mkToCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_mkToCtorIdxName___closed__0 = (const lean_object*)&l_mkToCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object*);
static const lean_string_object l_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_mkCtorIdxName___closed__0 = (const lean_object*)&l_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkCtorIdx_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkCtorIdx_spec__13___closed__0 = (const lean_object*)&l_panic___at___00mkCtorIdx_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-08-25"};
static const lean_object* l_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkCtorIdx___lam__1___closed__0_value)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__1_value;
static const lean_string_object l_mkCtorIdx___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_mkCtorIdx___lam__1___closed__2 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__2_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__3 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkCtorIdx"};
static const lean_object* l_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_mkCtorIdx___closed__0 = (const lean_object*)&l_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___closed__1;
static const lean_string_object l_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_mkCtorIdx___closed__2 = (const lean_object*)&l_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_73_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object* v_indName_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_mkToCtorIdxName___closed__0));
v___x_79_ = l_Lean_Name_str___override(v_indName_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object* v_indName_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_83_ = l_Lean_Name_str___override(v_indName_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object* v_env_84_, lean_object* v_declName_85_){
_start:
{
if (lean_obj_tag(v_declName_85_) == 1)
{
lean_object* v_pre_86_; lean_object* v_str_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_pre_86_ = lean_ctor_get(v_declName_85_, 0);
lean_inc(v_pre_86_);
v_str_87_ = lean_ctor_get(v_declName_85_, 1);
lean_inc_ref(v_str_87_);
lean_dec_ref(v_declName_85_);
v___x_88_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_89_ = lean_string_dec_eq(v_str_87_, v___x_88_);
lean_dec_ref(v_str_87_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v_pre_86_);
lean_dec_ref(v_env_84_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_isInductiveCore_x3f(v_env_84_, v_pre_86_);
return v___x_91_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_declName_85_);
lean_dec_ref(v_env_84_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object* v_declName_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_env_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_st_ref_get(v_a_94_);
v_env_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_96_);
v___x_98_ = l_isCtorIdxCore_x3f(v_env_97_, v_declName_93_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_isCtorIdx_x3f___redArg(v_declName_100_, v_a_101_);
lean_dec(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object* v_declName_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_isCtorIdx_x3f___redArg(v_declName_104_, v_a_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object* v_declName_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_isCtorIdx_x3f(v_declName_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
lean_object* v_name_120_; lean_object* v_defValue_121_; lean_object* v_map_122_; lean_object* v___x_123_; 
v_name_120_ = lean_ctor_get(v_opt_119_, 0);
v_defValue_121_ = lean_ctor_get(v_opt_119_, 1);
v_map_122_ = lean_ctor_get(v_opts_118_, 0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_122_, v_name_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_unbox(v_defValue_121_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; 
v_val_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v___x_123_);
if (lean_obj_tag(v_val_125_) == 1)
{
uint8_t v_v_126_; 
v_v_126_ = lean_ctor_get_uint8(v_val_125_, 0);
lean_dec_ref(v_val_125_);
return v_v_126_;
}
else
{
uint8_t v___x_127_; 
lean_dec(v_val_125_);
v___x_127_ = lean_unbox(v_defValue_121_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_opts_128_, v_opt_129_);
lean_dec_ref(v_opt_129_);
lean_dec_ref(v_opts_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object* v_constName_132_, uint8_t v_skipRealize_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; lean_object* v_env_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = lean_st_ref_get(v___y_134_);
v_env_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_env_137_);
lean_dec(v___x_136_);
v___x_138_ = l_Lean_Environment_contains(v_env_137_, v_constName_132_, v_skipRealize_133_);
v___x_139_ = lean_box(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_141_, lean_object* v_skipRealize_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
uint8_t v_skipRealize_boxed_145_; lean_object* v_res_146_; 
v_skipRealize_boxed_145_ = lean_unbox(v_skipRealize_142_);
v_res_146_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_141_, v_skipRealize_boxed_145_, v___y_143_);
lean_dec(v___y_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object* v_constName_147_, uint8_t v_skipRealize_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_147_, v_skipRealize_148_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object* v_constName_155_, lean_object* v_skipRealize_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_skipRealize_boxed_162_; lean_object* v_res_163_; 
v_skipRealize_boxed_162_ = lean_unbox(v_skipRealize_156_);
v_res_163_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1(v_constName_155_, v_skipRealize_boxed_162_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object* v_k_164_, lean_object* v_b_165_, lean_object* v_c_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_172_ = lean_apply_7(v_k_164_, v_b_165_, v_c_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, lean_box(0));
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_173_, lean_object* v_b_174_, lean_object* v_c_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(v_k_173_, v_b_174_, v_c_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object* v_type_182_, lean_object* v_maxFVars_x3f_183_, lean_object* v_k_184_, uint8_t v_cleanupAnnotations_185_, uint8_t v_whnfType_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___f_192_; lean_object* v___x_193_; 
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_192_, 0, v_k_184_);
v___x_193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_182_, v_maxFVars_x3f_183_, v___f_192_, v_cleanupAnnotations_185_, v_whnfType_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_193_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_193_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_210_, lean_object* v_maxFVars_x3f_211_, lean_object* v_k_212_, lean_object* v_cleanupAnnotations_213_, lean_object* v_whnfType_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_220_; uint8_t v_whnfType_boxed_221_; lean_object* v_res_222_; 
v_cleanupAnnotations_boxed_220_ = lean_unbox(v_cleanupAnnotations_213_);
v_whnfType_boxed_221_ = lean_unbox(v_whnfType_214_);
v_res_222_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_210_, v_maxFVars_x3f_211_, v_k_212_, v_cleanupAnnotations_boxed_220_, v_whnfType_boxed_221_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object* v_00_u03b1_223_, lean_object* v_type_224_, lean_object* v_maxFVars_x3f_225_, lean_object* v_k_226_, uint8_t v_cleanupAnnotations_227_, uint8_t v_whnfType_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_224_, v_maxFVars_x3f_225_, v_k_226_, v_cleanupAnnotations_227_, v_whnfType_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_235_, lean_object* v_type_236_, lean_object* v_maxFVars_x3f_237_, lean_object* v_k_238_, lean_object* v_cleanupAnnotations_239_, lean_object* v_whnfType_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_246_; uint8_t v_whnfType_boxed_247_; lean_object* v_res_248_; 
v_cleanupAnnotations_boxed_246_ = lean_unbox(v_cleanupAnnotations_239_);
v_whnfType_boxed_247_ = lean_unbox(v_whnfType_240_);
v_res_248_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(v_00_u03b1_235_, v_type_236_, v_maxFVars_x3f_237_, v_k_238_, v_cleanupAnnotations_boxed_246_, v_whnfType_boxed_247_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object* v_name_249_, lean_object* v_levelParams_250_, lean_object* v_type_251_, lean_object* v_value_252_, lean_object* v_hints_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; uint8_t v___y_258_; uint8_t v___y_265_; lean_object* v_env_268_; uint8_t v___x_269_; 
v___x_256_ = lean_st_ref_get(v___y_254_);
v_env_268_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref_n(v_env_268_, 2);
lean_dec(v___x_256_);
v___x_269_ = l_Lean_Environment_hasUnsafe(v_env_268_, v_type_251_);
if (v___x_269_ == 0)
{
uint8_t v___x_270_; 
v___x_270_ = l_Lean_Environment_hasUnsafe(v_env_268_, v_value_252_);
v___y_265_ = v___x_270_;
goto v___jp_264_;
}
else
{
lean_dec_ref(v_env_268_);
v___y_265_ = v___x_269_;
goto v___jp_264_;
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc(v_name_249_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v_name_249_);
lean_ctor_set(v___x_259_, 1, v_levelParams_250_);
lean_ctor_set(v___x_259_, 2, v_type_251_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v_name_249_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_262_, 0, v___x_259_);
lean_ctor_set(v___x_262_, 1, v_value_252_);
lean_ctor_set(v___x_262_, 2, v_hints_253_);
lean_ctor_set(v___x_262_, 3, v___x_261_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*4, v___y_258_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 1;
v___y_258_ = v___x_266_;
goto v___jp_257_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = 0;
v___y_258_ = v___x_267_;
goto v___jp_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_271_, lean_object* v_levelParams_272_, lean_object* v_type_273_, lean_object* v_value_274_, lean_object* v_hints_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_271_, v_levelParams_272_, v_type_273_, v_value_274_, v_hints_275_, v___y_276_);
lean_dec(v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object* v_name_279_, lean_object* v_levelParams_280_, lean_object* v_type_281_, lean_object* v_value_282_, lean_object* v_hints_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_279_, v_levelParams_280_, v_type_281_, v_value_282_, v_hints_283_, v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object* v_name_290_, lean_object* v_levelParams_291_, lean_object* v_type_292_, lean_object* v_value_293_, lean_object* v_hints_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(v_name_290_, v_levelParams_291_, v_type_292_, v_value_293_, v_hints_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___f_308_; lean_object* v___x_26913__overap_309_; lean_object* v___x_310_; 
v___f_308_ = ((lean_object*)(l_panic___at___00mkCtorIdx_spec__13___closed__0));
v___x_26913__overap_309_ = lean_panic_fn_borrowed(v___f_308_, v_msg_302_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
v___x_310_ = lean_apply_5(v___x_26913__overap_309_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, lean_box(0));
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_panic___at___00mkCtorIdx_spec__13(v_msg_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object* v___y_318_, uint8_t v_isExporting_319_, lean_object* v___x_320_, lean_object* v___y_321_, lean_object* v___x_322_, lean_object* v_a_x3f_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_traceState_330_; lean_object* v_messages_331_; lean_object* v_infoState_332_; lean_object* v_snapshotTasks_333_; lean_object* v_newDecls_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_359_; 
v___x_325_ = lean_st_ref_take(v___y_318_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_325_, 1);
v_ngen_328_ = lean_ctor_get(v___x_325_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_325_, 3);
v_traceState_330_ = lean_ctor_get(v___x_325_, 4);
v_messages_331_ = lean_ctor_get(v___x_325_, 6);
v_infoState_332_ = lean_ctor_get(v___x_325_, 7);
v_snapshotTasks_333_ = lean_ctor_get(v___x_325_, 8);
v_newDecls_334_ = lean_ctor_get(v___x_325_, 9);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v___x_325_, 5);
lean_dec(v_unused_360_);
v___x_336_ = v___x_325_;
v_isShared_337_ = v_isSharedCheck_359_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_newDecls_334_);
lean_inc(v_snapshotTasks_333_);
lean_inc(v_infoState_332_);
lean_inc(v_messages_331_);
lean_inc(v_traceState_330_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_325_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_359_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = l_Lean_Environment_setExporting(v_env_326_, v_isExporting_319_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 5, v___x_320_);
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v_traceState_330_);
lean_ctor_set(v_reuseFailAlloc_358_, 5, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_358_, 6, v_messages_331_);
lean_ctor_set(v_reuseFailAlloc_358_, 7, v_infoState_332_);
lean_ctor_set(v_reuseFailAlloc_358_, 8, v_snapshotTasks_333_);
lean_ctor_set(v_reuseFailAlloc_358_, 9, v_newDecls_334_);
v___x_340_ = v_reuseFailAlloc_358_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_mctx_343_; lean_object* v_zetaDeltaFVarIds_344_; lean_object* v_postponed_345_; lean_object* v_diag_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v___x_341_ = lean_st_ref_set(v___y_318_, v___x_340_);
v___x_342_ = lean_st_ref_take(v___y_321_);
v_mctx_343_ = lean_ctor_get(v___x_342_, 0);
v_zetaDeltaFVarIds_344_ = lean_ctor_get(v___x_342_, 2);
v_postponed_345_ = lean_ctor_get(v___x_342_, 3);
v_diag_346_ = lean_ctor_get(v___x_342_, 4);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v___x_342_, 1);
lean_dec(v_unused_357_);
v___x_348_ = v___x_342_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_diag_346_);
lean_inc(v_postponed_345_);
lean_inc(v_zetaDeltaFVarIds_344_);
lean_inc(v_mctx_343_);
lean_dec(v___x_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_322_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_mctx_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_zetaDeltaFVarIds_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_postponed_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_diag_346_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_st_ref_set(v___y_321_, v___x_351_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object* v___y_361_, lean_object* v_isExporting_362_, lean_object* v___x_363_, lean_object* v___y_364_, lean_object* v___x_365_, lean_object* v_a_x3f_366_, lean_object* v___y_367_){
_start:
{
uint8_t v_isExporting_boxed_368_; lean_object* v_res_369_; 
v_isExporting_boxed_368_ = lean_unbox(v_isExporting_362_);
v_res_369_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_361_, v_isExporting_boxed_368_, v___x_363_, v___y_364_, v___x_365_, v_a_x3f_366_);
lean_dec(v_a_x3f_366_);
lean_dec(v___y_364_);
lean_dec(v___y_361_);
return v_res_369_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_370_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_376_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
lean_ctor_set(v___x_376_, 2, v___x_375_);
lean_ctor_set(v___x_376_, 3, v___x_375_);
lean_ctor_set(v___x_376_, 4, v___x_375_);
lean_ctor_set(v___x_376_, 5, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object* v_x_377_, uint8_t v_isExporting_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; lean_object* v_env_385_; uint8_t v_isExporting_386_; lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v_nextMacroScope_389_; lean_object* v_ngen_390_; lean_object* v_auxDeclNGen_391_; lean_object* v_traceState_392_; lean_object* v_messages_393_; lean_object* v_infoState_394_; lean_object* v_snapshotTasks_395_; lean_object* v_newDecls_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_450_; 
v___x_384_ = lean_st_ref_get(v___y_382_);
v_env_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_385_);
lean_dec(v___x_384_);
v_isExporting_386_ = lean_ctor_get_uint8(v_env_385_, sizeof(void*)*8);
lean_dec_ref(v_env_385_);
v___x_387_ = lean_st_ref_take(v___y_382_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
v_nextMacroScope_389_ = lean_ctor_get(v___x_387_, 1);
v_ngen_390_ = lean_ctor_get(v___x_387_, 2);
v_auxDeclNGen_391_ = lean_ctor_get(v___x_387_, 3);
v_traceState_392_ = lean_ctor_get(v___x_387_, 4);
v_messages_393_ = lean_ctor_get(v___x_387_, 6);
v_infoState_394_ = lean_ctor_get(v___x_387_, 7);
v_snapshotTasks_395_ = lean_ctor_get(v___x_387_, 8);
v_newDecls_396_ = lean_ctor_get(v___x_387_, 9);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_387_, 5);
lean_dec(v_unused_451_);
v___x_398_ = v___x_387_;
v_isShared_399_ = v_isSharedCheck_450_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_newDecls_396_);
lean_inc(v_snapshotTasks_395_);
lean_inc(v_infoState_394_);
lean_inc(v_messages_393_);
lean_inc(v_traceState_392_);
lean_inc(v_auxDeclNGen_391_);
lean_inc(v_ngen_390_);
lean_inc(v_nextMacroScope_389_);
lean_inc(v_env_388_);
lean_dec(v___x_387_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_450_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_400_ = l_Lean_Environment_setExporting(v_env_388_, v_isExporting_378_);
v___x_401_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 5, v___x_401_);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_nextMacroScope_389_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_ngen_390_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_auxDeclNGen_391_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_traceState_392_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_messages_393_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_infoState_394_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_snapshotTasks_395_);
lean_ctor_set(v_reuseFailAlloc_449_, 9, v_newDecls_396_);
v___x_403_ = v_reuseFailAlloc_449_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_mctx_406_; lean_object* v_zetaDeltaFVarIds_407_; lean_object* v_postponed_408_; lean_object* v_diag_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_447_; 
v___x_404_ = lean_st_ref_set(v___y_382_, v___x_403_);
v___x_405_ = lean_st_ref_take(v___y_380_);
v_mctx_406_ = lean_ctor_get(v___x_405_, 0);
v_zetaDeltaFVarIds_407_ = lean_ctor_get(v___x_405_, 2);
v_postponed_408_ = lean_ctor_get(v___x_405_, 3);
v_diag_409_ = lean_ctor_get(v___x_405_, 4);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_405_, 1);
lean_dec(v_unused_448_);
v___x_411_ = v___x_405_;
v_isShared_412_ = v_isSharedCheck_447_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_diag_409_);
lean_inc(v_postponed_408_);
lean_inc(v_zetaDeltaFVarIds_407_);
lean_inc(v_mctx_406_);
lean_dec(v___x_405_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_447_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_mctx_406_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_zetaDeltaFVarIds_407_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_postponed_408_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_diag_409_);
v___x_415_ = v_reuseFailAlloc_446_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v_r_417_; 
v___x_416_ = lean_st_ref_set(v___y_380_, v___x_415_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
v_r_417_ = lean_apply_5(v_x_377_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, lean_box(0));
if (lean_obj_tag(v_r_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_434_; 
v_a_418_ = lean_ctor_get(v_r_417_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_r_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_420_ = v_r_417_;
v_isShared_421_ = v_isSharedCheck_434_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v_r_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_434_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
lean_inc(v_a_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 1);
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_433_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v___x_424_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_382_, v_isExporting_386_, v___x_401_, v___y_380_, v___x_413_, v___x_423_);
lean_dec_ref(v___x_423_);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_432_);
v___x_426_ = v___x_424_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_dec(v___x_424_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_a_418_);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_418_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_435_ = lean_ctor_get(v_r_417_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v_r_417_);
v___x_436_ = lean_box(0);
v___x_437_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_382_, v_isExporting_386_, v___x_401_, v___y_380_, v___x_413_, v___x_436_);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_445_);
v___x_439_ = v___x_437_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_dec(v___x_437_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 1);
lean_ctor_set(v___x_439_, 0, v_a_435_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_435_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_452_, lean_object* v_isExporting_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_isExporting_boxed_459_; lean_object* v_res_460_; 
v_isExporting_boxed_459_ = lean_unbox(v_isExporting_453_);
v_res_460_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_452_, v_isExporting_boxed_459_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object* v_00_u03b1_461_, lean_object* v_x_462_, uint8_t v_isExporting_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_462_, v_isExporting_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_470_, lean_object* v_x_471_, lean_object* v_isExporting_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
uint8_t v_isExporting_boxed_478_; lean_object* v_res_479_; 
v_isExporting_boxed_478_ = lean_unbox(v_isExporting_472_);
v_res_479_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14(v_00_u03b1_470_, v_x_471_, v_isExporting_boxed_478_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; lean_object* v_env_487_; lean_object* v___x_488_; lean_object* v_mctx_489_; lean_object* v_lctx_490_; lean_object* v_options_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_486_ = lean_st_ref_get(v___y_484_);
v_env_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc_ref(v_env_487_);
lean_dec(v___x_486_);
v___x_488_ = lean_st_ref_get(v___y_482_);
v_mctx_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc_ref(v_mctx_489_);
lean_dec(v___x_488_);
v_lctx_490_ = lean_ctor_get(v___y_481_, 2);
v_options_491_ = lean_ctor_get(v___y_483_, 2);
lean_inc_ref(v_options_491_);
lean_inc_ref(v_lctx_490_);
v___x_492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_492_, 0, v_env_487_);
lean_ctor_set(v___x_492_, 1, v_mctx_489_);
lean_ctor_set(v___x_492_, 2, v_lctx_490_);
lean_ctor_set(v___x_492_, 3, v_options_491_);
v___x_493_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_msgData_480_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_ref_508_; lean_object* v___x_509_; lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_ref_508_ = lean_ctor_get(v___y_505_, 5);
v___x_509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msg_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
lean_inc(v_ref_508_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_ref_508_);
lean_ctor_set(v___x_514_, 1, v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_instMonadEIO(lean_box(0));
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_toApplicative_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_600_; 
v___x_537_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
v___x_538_ = l_StateRefT_x27_instMonad___redArg(v___x_537_);
v_toApplicative_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_538_, 1);
lean_dec(v_unused_601_);
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_600_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_toApplicative_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_600_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_toFunctor_543_; lean_object* v_toSeq_544_; lean_object* v_toSeqLeft_545_; lean_object* v_toSeqRight_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_598_; 
v_toFunctor_543_ = lean_ctor_get(v_toApplicative_539_, 0);
v_toSeq_544_ = lean_ctor_get(v_toApplicative_539_, 2);
v_toSeqLeft_545_ = lean_ctor_get(v_toApplicative_539_, 3);
v_toSeqRight_546_ = lean_ctor_get(v_toApplicative_539_, 4);
v_isSharedCheck_598_ = !lean_is_exclusive(v_toApplicative_539_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_toApplicative_539_, 1);
lean_dec(v_unused_599_);
v___x_548_ = v_toApplicative_539_;
v_isShared_549_ = v_isSharedCheck_598_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_toSeqRight_546_);
lean_inc(v_toSeqLeft_545_);
lean_inc(v_toSeq_544_);
lean_inc(v_toFunctor_543_);
lean_dec(v_toApplicative_539_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_598_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___f_556_; lean_object* v___f_557_; lean_object* v___x_559_; 
v___f_550_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1));
v___f_551_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_543_);
v___f_552_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_552_, 0, v_toFunctor_543_);
v___f_553_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_553_, 0, v_toFunctor_543_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___f_552_);
lean_ctor_set(v___x_554_, 1, v___f_553_);
v___f_555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_555_, 0, v_toSeqRight_546_);
v___f_556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_556_, 0, v_toSeqLeft_545_);
v___f_557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_557_, 0, v_toSeq_544_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 4, v___f_555_);
lean_ctor_set(v___x_548_, 3, v___f_556_);
lean_ctor_set(v___x_548_, 2, v___f_557_);
lean_ctor_set(v___x_548_, 1, v___f_550_);
lean_ctor_set(v___x_548_, 0, v___x_554_);
v___x_559_ = v___x_548_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___f_550_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___f_557_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v___f_556_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v___f_555_);
v___x_559_ = v_reuseFailAlloc_597_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___f_551_);
lean_ctor_set(v___x_541_, 0, v___x_559_);
v___x_561_ = v___x_541_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___f_551_);
v___x_561_ = v_reuseFailAlloc_596_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v_toApplicative_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_594_; 
v___x_562_ = l_StateRefT_x27_instMonad___redArg(v___x_561_);
v_toApplicative_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v___x_562_, 1);
lean_dec(v_unused_595_);
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_594_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_toApplicative_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_594_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_toFunctor_567_; lean_object* v_toSeq_568_; lean_object* v_toSeqLeft_569_; lean_object* v_toSeqRight_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_592_; 
v_toFunctor_567_ = lean_ctor_get(v_toApplicative_563_, 0);
v_toSeq_568_ = lean_ctor_get(v_toApplicative_563_, 2);
v_toSeqLeft_569_ = lean_ctor_get(v_toApplicative_563_, 3);
v_toSeqRight_570_ = lean_ctor_get(v_toApplicative_563_, 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v_toApplicative_563_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v_toApplicative_563_, 1);
lean_dec(v_unused_593_);
v___x_572_ = v_toApplicative_563_;
v_isShared_573_ = v_isSharedCheck_592_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_toSeqRight_570_);
lean_inc(v_toSeqLeft_569_);
lean_inc(v_toSeq_568_);
lean_inc(v_toFunctor_567_);
lean_dec(v_toApplicative_563_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_592_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___f_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___x_583_; 
v___f_574_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3));
v___f_575_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_567_);
v___f_576_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_576_, 0, v_toFunctor_567_);
v___f_577_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_577_, 0, v_toFunctor_567_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___f_576_);
lean_ctor_set(v___x_578_, 1, v___f_577_);
v___f_579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_579_, 0, v_toSeqRight_570_);
v___f_580_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_580_, 0, v_toSeqLeft_569_);
v___f_581_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_581_, 0, v_toSeq_568_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 4, v___f_579_);
lean_ctor_set(v___x_572_, 3, v___f_580_);
lean_ctor_set(v___x_572_, 2, v___f_581_);
lean_ctor_set(v___x_572_, 1, v___f_574_);
lean_ctor_set(v___x_572_, 0, v___x_578_);
v___x_583_ = v___x_572_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___f_574_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v___f_581_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v___f_580_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v___f_579_);
v___x_583_ = v_reuseFailAlloc_591_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___f_575_);
lean_ctor_set(v___x_565_, 0, v___x_583_);
v___x_585_ = v___x_565_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___f_575_);
v___x_585_ = v_reuseFailAlloc_590_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_30307__overap_588_; lean_object* v___x_589_; 
v___x_586_ = lean_box(0);
v___x_587_ = l_instInhabitedOfMonad___redArg(v___x_585_, v___x_586_);
v___x_30307__overap_588_ = lean_panic_fn_borrowed(v___x_587_, v_msg_531_);
lean_dec(v___x_587_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
v___x_589_ = lean_apply_5(v___x_30307__overap_588_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, lean_box(0));
return v___x_589_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v_msg_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_608_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_618_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_619_ = lean_unsigned_to_nat(11u);
v___x_620_ = lean_unsigned_to_nat(122u);
v___x_621_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5));
v___x_622_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4));
v___x_623_ = l_mkPanicMessageWithDecl(v___x_622_, v___x_621_, v___x_620_, v___x_619_, v___x_618_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object* v_constName_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_638_; lean_object* v_env_639_; uint8_t v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_st_ref_get(v___y_628_);
v_env_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_env_639_);
lean_dec(v___x_638_);
v___x_640_ = 0;
lean_inc(v_constName_624_);
v___x_641_ = l_Lean_Environment_findAsync_x3f(v_env_639_, v_constName_624_, v___x_640_);
if (lean_obj_tag(v___x_641_) == 1)
{
lean_object* v_val_642_; uint8_t v_kind_643_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref(v___x_641_);
v_kind_643_ = lean_ctor_get_uint8(v_val_642_, sizeof(void*)*3);
if (v_kind_643_ == 6)
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_642_);
if (lean_obj_tag(v___x_644_) == 6)
{
lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_constName_624_);
v_val_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_val_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref(v___x_644_);
v___x_653_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7);
v___x_654_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v___x_653_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
if (lean_obj_tag(v_a_655_) == 0)
{
lean_del_object(v___x_657_);
goto v___jp_630_;
}
else
{
lean_object* v_val_659_; lean_object* v___x_661_; 
lean_dec(v_constName_624_);
v_val_659_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_val_659_);
lean_dec_ref(v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_val_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_val_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_constName_624_);
v_a_664_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_654_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_654_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
else
{
lean_dec(v_val_642_);
goto v___jp_630_;
}
}
else
{
lean_dec(v___x_641_);
goto v___jp_630_;
}
v___jp_630_:
{
lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_631_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_632_ = 0;
v___x_633_ = l_Lean_MessageData_ofConstName(v_constName_624_, v___x_632_);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_631_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_636_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object* v_constName_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_constName_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_679_, uint8_t v___x_680_, uint8_t v___x_681_, uint8_t v___x_682_, lean_object* v_ys_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = l_Lean_mkRawNatLit(v_cidx_679_);
v___x_691_ = l_Lean_Meta_mkLambdaFVars(v_ys_683_, v___x_690_, v___x_680_, v___x_681_, v___x_680_, v___x_681_, v___x_682_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v_ys_696_, lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v___x_35139__boxed_703_; uint8_t v___x_35140__boxed_704_; uint8_t v___x_35141__boxed_705_; lean_object* v_res_706_; 
v___x_35139__boxed_703_ = lean_unbox(v___x_693_);
v___x_35140__boxed_704_ = lean_unbox(v___x_694_);
v___x_35141__boxed_705_ = lean_unbox(v___x_695_);
v_res_706_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(v_cidx_692_, v___x_35139__boxed_703_, v___x_35140__boxed_704_, v___x_35141__boxed_705_, v_ys_696_, v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_x_697_);
lean_dec_ref(v_ys_696_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t v___x_707_, lean_object* v___x_708_, lean_object* v_as_x27_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
if (lean_obj_tag(v_as_x27_709_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_b_710_);
return v___x_716_;
}
else
{
lean_object* v_head_717_; lean_object* v_tail_718_; lean_object* v___x_719_; 
v_head_717_ = lean_ctor_get(v_as_x27_709_, 0);
v_tail_718_ = lean_ctor_get(v_as_x27_709_, 1);
lean_inc(v_head_717_);
v___x_719_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_head_717_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v_toConstantVal_721_; lean_object* v_cidx_722_; lean_object* v_numFields_723_; lean_object* v_type_724_; lean_object* v___x_725_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
v_toConstantVal_721_ = lean_ctor_get(v_a_720_, 0);
lean_inc_ref(v_toConstantVal_721_);
v_cidx_722_ = lean_ctor_get(v_a_720_, 2);
lean_inc(v_cidx_722_);
v_numFields_723_ = lean_ctor_get(v_a_720_, 4);
lean_inc(v_numFields_723_);
lean_dec(v_a_720_);
v_type_724_ = lean_ctor_get(v_toConstantVal_721_, 2);
lean_inc_ref(v_type_724_);
lean_dec_ref(v_toConstantVal_721_);
v___x_725_ = l_Lean_Meta_instantiateForall(v_type_724_, v___x_708_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_743_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_743_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_743_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_743_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___x_737_; 
v___x_730_ = 0;
v___x_731_ = 1;
v___x_732_ = lean_box(v___x_730_);
v___x_733_ = lean_box(v___x_707_);
v___x_734_ = lean_box(v___x_731_);
v___f_735_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_735_, 0, v_cidx_722_);
lean_closure_set(v___f_735_, 1, v___x_732_);
lean_closure_set(v___f_735_, 2, v___x_733_);
lean_closure_set(v___f_735_, 3, v___x_734_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 1);
lean_ctor_set(v___x_728_, 0, v_numFields_723_);
v___x_737_ = v___x_728_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_numFields_723_);
v___x_737_ = v_reuseFailAlloc_742_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_a_726_, v___x_737_, v___f_735_, v___x_730_, v___x_730_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_Expr_app___override(v_b_710_, v_a_739_);
v_as_x27_709_ = v_tail_718_;
v_b_710_ = v___x_740_;
goto _start;
}
else
{
lean_dec_ref(v_b_710_);
return v___x_738_;
}
}
}
}
else
{
lean_dec(v_numFields_723_);
lean_dec(v_cidx_722_);
lean_dec_ref(v_b_710_);
return v___x_725_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_b_710_);
v_a_744_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_719_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_719_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_752_, lean_object* v___x_753_, lean_object* v_as_x27_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v___x_35170__boxed_761_; lean_object* v_res_762_; 
v___x_35170__boxed_761_ = lean_unbox(v___x_752_);
v_res_762_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_35170__boxed_761_, v___x_753_, v_as_x27_754_, v_b_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v_as_x27_754_);
lean_dec_ref(v___x_753_);
return v_res_762_;
}
}
static lean_object* _init_l_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_box(0);
v___x_764_ = l_Lean_Level_succ___override(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object* v_xs_765_, uint8_t v___x_766_, uint8_t v___x_767_, uint8_t v___x_768_, lean_object* v_val_769_, lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v_ctors_775_, lean_object* v___x_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_value_784_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_787_ = l_Lean_InductiveVal_numCtors(v_val_769_);
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_dec_eq(v___x_787_, v___x_788_);
lean_dec(v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v___x_776_);
lean_inc_ref(v_x_777_);
lean_inc_ref(v___x_770_);
v___x_790_ = lean_array_push(v___x_770_, v_x_777_);
v___x_791_ = l_Lean_Meta_mkLambdaFVars(v___x_790_, v___x_771_, v___x_766_, v___x_767_, v___x_766_, v___x_767_, v___x_768_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec_ref(v___x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
v___x_793_ = lean_obj_once(&l_mkCtorIdx___lam__0___closed__0, &l_mkCtorIdx___lam__0___closed__0_once, _init_l_mkCtorIdx___lam__0___closed__0);
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_772_);
v___x_795_ = l_Lean_mkConst(v___x_773_, v___x_794_);
v___x_796_ = l_Lean_mkAppN(v___x_795_, v___x_774_);
v___x_797_ = l_Lean_Expr_app___override(v___x_796_, v_a_792_);
v___x_798_ = l_Lean_mkAppN(v___x_797_, v___x_770_);
lean_dec_ref(v___x_770_);
lean_inc_ref(v_x_777_);
v___x_799_ = l_Lean_Expr_app___override(v___x_798_, v_x_777_);
v___x_800_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_767_, v___x_774_, v_ctors_775_, v___x_799_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v_value_784_ = v_a_801_;
goto v___jp_783_;
}
else
{
lean_dec_ref(v_x_777_);
lean_dec_ref(v_xs_765_);
return v___x_800_;
}
}
else
{
lean_dec_ref(v_x_777_);
lean_dec(v___x_773_);
lean_dec(v___x_772_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v_xs_765_);
return v___x_791_;
}
}
else
{
lean_object* v___x_802_; 
lean_dec(v___x_773_);
lean_dec(v___x_772_);
lean_dec_ref(v___x_771_);
lean_dec_ref(v___x_770_);
v___x_802_ = l_Lean_mkRawNatLit(v___x_776_);
v_value_784_ = v___x_802_;
goto v___jp_783_;
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_array_push(v_xs_765_, v_x_777_);
v___x_786_ = l_Lean_Meta_mkLambdaFVars(v___x_785_, v_value_784_, v___x_766_, v___x_767_, v___x_766_, v___x_767_, v___x_768_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec_ref(v___x_785_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_803_ = _args[0];
lean_object* v___x_804_ = _args[1];
lean_object* v___x_805_ = _args[2];
lean_object* v___x_806_ = _args[3];
lean_object* v_val_807_ = _args[4];
lean_object* v___x_808_ = _args[5];
lean_object* v___x_809_ = _args[6];
lean_object* v___x_810_ = _args[7];
lean_object* v___x_811_ = _args[8];
lean_object* v___x_812_ = _args[9];
lean_object* v_ctors_813_ = _args[10];
lean_object* v___x_814_ = _args[11];
lean_object* v_x_815_ = _args[12];
lean_object* v___y_816_ = _args[13];
lean_object* v___y_817_ = _args[14];
lean_object* v___y_818_ = _args[15];
lean_object* v___y_819_ = _args[16];
lean_object* v___y_820_ = _args[17];
_start:
{
uint8_t v___x_35261__boxed_821_; uint8_t v___x_35262__boxed_822_; uint8_t v___x_35263__boxed_823_; lean_object* v_res_824_; 
v___x_35261__boxed_821_ = lean_unbox(v___x_804_);
v___x_35262__boxed_822_ = lean_unbox(v___x_805_);
v___x_35263__boxed_823_ = lean_unbox(v___x_806_);
v_res_824_ = l_mkCtorIdx___lam__0(v_xs_803_, v___x_35261__boxed_821_, v___x_35262__boxed_822_, v___x_35263__boxed_823_, v_val_807_, v___x_808_, v___x_809_, v___x_810_, v___x_811_, v___x_812_, v_ctors_813_, v___x_814_, v_x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v_ctors_813_);
lean_dec_ref(v___x_812_);
lean_dec_ref(v_val_807_);
return v_res_824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
lean_ctor_set(v___x_830_, 3, v___x_829_);
lean_ctor_set(v___x_830_, 4, v___x_828_);
lean_ctor_set(v___x_830_, 5, v___x_828_);
lean_ctor_set(v___x_830_, 6, v___x_828_);
lean_ctor_set(v___x_830_, 7, v___x_828_);
lean_ctor_set(v___x_830_, 8, v___x_828_);
lean_ctor_set(v___x_830_, 9, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(32u);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = ((size_t)5ULL);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_unsigned_to_nat(32u);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
v___x_838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_839_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_837_);
lean_ctor_set(v___x_839_, 2, v___x_835_);
lean_ctor_set(v___x_839_, 3, v___x_835_);
lean_ctor_set_usize(v___x_839_, 4, v___x_834_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = lean_box(1);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v___x_841_);
lean_ctor_set(v___x_843_, 2, v___x_840_);
return v___x_843_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_env_870_; uint8_t v___x_871_; 
v___x_869_ = lean_st_ref_get(v___y_867_);
v_env_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_env_870_);
lean_dec(v___x_869_);
v___x_871_ = l_Lean_Name_isAnonymous(v_declHint_866_);
if (v___x_871_ == 0)
{
uint8_t v_isExporting_872_; 
v_isExporting_872_ = lean_ctor_get_uint8(v_env_870_, sizeof(void*)*8);
if (v_isExporting_872_ == 0)
{
lean_object* v___x_873_; 
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_msg_865_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; uint8_t v___x_875_; 
lean_inc_ref(v_env_870_);
v___x_874_ = l_Lean_Environment_setExporting(v_env_870_, v___x_871_);
lean_inc(v_declHint_866_);
lean_inc_ref(v___x_874_);
v___x_875_ = l_Lean_Environment_contains(v___x_874_, v_declHint_866_, v_isExporting_872_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_msg_865_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_c_882_; lean_object* v___x_883_; 
v___x_877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_878_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_879_ = l_Lean_Options_empty;
v___x_880_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_880_, 0, v___x_874_);
lean_ctor_set(v___x_880_, 1, v___x_877_);
lean_ctor_set(v___x_880_, 2, v___x_878_);
lean_ctor_set(v___x_880_, 3, v___x_879_);
lean_inc(v_declHint_866_);
v___x_881_ = l_Lean_MessageData_ofConstName(v_declHint_866_, v___x_871_);
v_c_882_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_882_, 0, v___x_880_);
lean_ctor_set(v_c_882_, 1, v___x_881_);
v___x_883_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_870_, v_declHint_866_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_c_882_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_note(v___x_887_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v_msg_865_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
else
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_926_; 
v_val_891_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_926_ == 0)
{
v___x_893_ = v___x_883_;
v_isShared_894_ = v_isSharedCheck_926_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v___x_883_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_926_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_mod_898_; uint8_t v___x_899_; 
v___x_895_ = lean_box(0);
v___x_896_ = l_Lean_Environment_header(v_env_870_);
lean_dec_ref(v_env_870_);
v___x_897_ = l_Lean_EnvironmentHeader_moduleNames(v___x_896_);
v_mod_898_ = lean_array_get(v___x_895_, v___x_897_, v_val_891_);
lean_dec(v_val_891_);
lean_dec_ref(v___x_897_);
v___x_899_ = l_Lean_isPrivateName(v_declHint_866_);
lean_dec(v_declHint_866_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_c_882_);
v___x_902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_MessageData_ofName(v_mod_898_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_MessageData_note(v___x_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v_msg_865_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 0);
lean_ctor_set(v___x_893_, 0, v___x_909_);
v___x_911_ = v___x_893_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_c_882_);
v___x_915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_MessageData_ofName(v_mod_898_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_MessageData_note(v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v_msg_865_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 0);
lean_ctor_set(v___x_893_, 0, v___x_922_);
v___x_924_ = v___x_893_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_msg_865_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_928_, lean_object* v_declHint_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_928_, v_declHint_929_, v___y_930_);
lean_dec(v___y_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_933_, lean_object* v_declHint_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_950_; 
v___x_940_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_933_, v_declHint_934_, v___y_938_);
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_950_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_950_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_950_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = l_Lean_unknownIdentifierMessageTag;
v___x_946_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_a_941_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_951_, lean_object* v_declHint_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_951_, v_declHint_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_959_, lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_fileName_966_; lean_object* v_fileMap_967_; lean_object* v_options_968_; lean_object* v_currRecDepth_969_; lean_object* v_maxRecDepth_970_; lean_object* v_ref_971_; lean_object* v_currNamespace_972_; lean_object* v_openDecls_973_; lean_object* v_initHeartbeats_974_; lean_object* v_maxHeartbeats_975_; lean_object* v_quotContext_976_; lean_object* v_currMacroScope_977_; uint8_t v_diag_978_; lean_object* v_cancelTk_x3f_979_; uint8_t v_suppressElabErrors_980_; lean_object* v_inheritedTraceOptions_981_; lean_object* v_ref_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_fileName_966_ = lean_ctor_get(v___y_963_, 0);
v_fileMap_967_ = lean_ctor_get(v___y_963_, 1);
v_options_968_ = lean_ctor_get(v___y_963_, 2);
v_currRecDepth_969_ = lean_ctor_get(v___y_963_, 3);
v_maxRecDepth_970_ = lean_ctor_get(v___y_963_, 4);
v_ref_971_ = lean_ctor_get(v___y_963_, 5);
v_currNamespace_972_ = lean_ctor_get(v___y_963_, 6);
v_openDecls_973_ = lean_ctor_get(v___y_963_, 7);
v_initHeartbeats_974_ = lean_ctor_get(v___y_963_, 8);
v_maxHeartbeats_975_ = lean_ctor_get(v___y_963_, 9);
v_quotContext_976_ = lean_ctor_get(v___y_963_, 10);
v_currMacroScope_977_ = lean_ctor_get(v___y_963_, 11);
v_diag_978_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*14);
v_cancelTk_x3f_979_ = lean_ctor_get(v___y_963_, 12);
v_suppressElabErrors_980_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_981_ = lean_ctor_get(v___y_963_, 13);
v_ref_982_ = l_Lean_replaceRef(v_ref_959_, v_ref_971_);
lean_inc_ref(v_inheritedTraceOptions_981_);
lean_inc(v_cancelTk_x3f_979_);
lean_inc(v_currMacroScope_977_);
lean_inc(v_quotContext_976_);
lean_inc(v_maxHeartbeats_975_);
lean_inc(v_initHeartbeats_974_);
lean_inc(v_openDecls_973_);
lean_inc(v_currNamespace_972_);
lean_inc(v_maxRecDepth_970_);
lean_inc(v_currRecDepth_969_);
lean_inc_ref(v_options_968_);
lean_inc_ref(v_fileMap_967_);
lean_inc_ref(v_fileName_966_);
v___x_983_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_983_, 0, v_fileName_966_);
lean_ctor_set(v___x_983_, 1, v_fileMap_967_);
lean_ctor_set(v___x_983_, 2, v_options_968_);
lean_ctor_set(v___x_983_, 3, v_currRecDepth_969_);
lean_ctor_set(v___x_983_, 4, v_maxRecDepth_970_);
lean_ctor_set(v___x_983_, 5, v_ref_982_);
lean_ctor_set(v___x_983_, 6, v_currNamespace_972_);
lean_ctor_set(v___x_983_, 7, v_openDecls_973_);
lean_ctor_set(v___x_983_, 8, v_initHeartbeats_974_);
lean_ctor_set(v___x_983_, 9, v_maxHeartbeats_975_);
lean_ctor_set(v___x_983_, 10, v_quotContext_976_);
lean_ctor_set(v___x_983_, 11, v_currMacroScope_977_);
lean_ctor_set(v___x_983_, 12, v_cancelTk_x3f_979_);
lean_ctor_set(v___x_983_, 13, v_inheritedTraceOptions_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*14, v_diag_978_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*14 + 1, v_suppressElabErrors_980_);
v___x_984_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_960_, v___y_961_, v___y_962_, v___x_983_, v___y_964_);
lean_dec_ref(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_985_, v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v_ref_985_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_993_, lean_object* v_msg_994_, lean_object* v_declHint_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v_a_1002_; lean_object* v___x_1003_; 
v___x_1001_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_994_, v_declHint_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_993_, v_a_1002_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1004_, lean_object* v_msg_1005_, lean_object* v_declHint_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1004_, v_msg_1005_, v_declHint_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v_ref_1004_);
return v_res_1012_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1016_, lean_object* v_constName_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1023_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1024_ = 0;
lean_inc(v_constName_1017_);
v___x_1025_ = l_Lean_MessageData_ofConstName(v_constName_1017_, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1023_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1016_, v___x_1028_, v_constName_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1030_, lean_object* v_constName_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1030_, v_constName_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v_ref_1030_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_ref_1044_; lean_object* v___x_1045_; 
v_ref_1044_ = lean_ctor_get(v___y_1041_, 5);
v___x_1045_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1044_, v_constName_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object* v_constName_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v_env_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1059_ = lean_st_ref_get(v___y_1057_);
v_env_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_ref(v_env_1060_);
lean_dec(v___x_1059_);
v___x_1061_ = 0;
lean_inc(v_constName_1053_);
v___x_1062_ = l_Lean_Environment_find_x3f(v_env_1060_, v_constName_1053_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1063_;
}
else
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_constName_1053_);
v_val_1064_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1062_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_val_1064_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object* v_constName_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_constName_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t v___x_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = 1;
v___x_1087_ = lean_box(v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v_head_1089_; lean_object* v_tail_1090_; lean_object* v___x_1091_; 
v_head_1089_ = lean_ctor_get(v_x_1080_, 0);
lean_inc(v_head_1089_);
v_tail_1090_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_tail_1090_);
lean_dec_ref(v_x_1080_);
v___x_1091_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_head_1089_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1112_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1112_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1112_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___y_1097_; uint8_t v_a_1098_; 
if (lean_obj_tag(v_a_1092_) == 6)
{
lean_object* v_val_1100_; lean_object* v_numFields_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v_val_1100_ = lean_ctor_get(v_a_1092_, 0);
lean_inc_ref(v_val_1100_);
lean_dec_ref(v_a_1092_);
v_numFields_1101_ = lean_ctor_get(v_val_1100_, 4);
lean_inc(v_numFields_1101_);
lean_dec_ref(v_val_1100_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_nat_dec_eq(v_numFields_1101_, v___x_1102_);
lean_dec(v_numFields_1101_);
v___x_1104_ = lean_box(v___x_1103_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1104_);
v___x_1106_ = v___x_1094_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1097_ = v___x_1106_;
v_a_1098_ = v___x_1103_;
goto v___jp_1096_;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec(v_a_1092_);
v___x_1108_ = lean_box(v___x_1079_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1108_);
v___x_1110_ = v___x_1094_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v___y_1097_ = v___x_1110_;
v_a_1098_ = v___x_1079_;
goto v___jp_1096_;
}
}
v___jp_1096_:
{
if (v_a_1098_ == 0)
{
lean_dec(v_tail_1090_);
return v___y_1097_;
}
else
{
lean_dec_ref(v___y_1097_);
v_x_1080_ = v_tail_1090_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_tail_1090_);
v_a_1113_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1091_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1091_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_35781__boxed_1128_; lean_object* v_res_1129_; 
v___x_35781__boxed_1128_ = lean_unbox(v___x_1121_);
v_res_1129_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v___x_35781__boxed_1128_, v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object* v_declName_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_declName_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1192_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1192_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1192_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
if (lean_obj_tag(v_a_1137_) == 5)
{
lean_object* v_val_1141_; lean_object* v_toConstantVal_1142_; lean_object* v_numParams_1143_; lean_object* v_numIndices_1144_; lean_object* v_ctors_1145_; uint8_t v_isRec_1146_; uint8_t v_isUnsafe_1147_; lean_object* v_type_1148_; uint8_t v___x_1149_; 
v_val_1141_ = lean_ctor_get(v_a_1137_, 0);
lean_inc_ref(v_val_1141_);
lean_dec_ref(v_a_1137_);
v_toConstantVal_1142_ = lean_ctor_get(v_val_1141_, 0);
v_numParams_1143_ = lean_ctor_get(v_val_1141_, 1);
lean_inc(v_numParams_1143_);
v_numIndices_1144_ = lean_ctor_get(v_val_1141_, 2);
lean_inc(v_numIndices_1144_);
v_ctors_1145_ = lean_ctor_get(v_val_1141_, 4);
lean_inc(v_ctors_1145_);
v_isRec_1146_ = lean_ctor_get_uint8(v_val_1141_, sizeof(void*)*6);
v_isUnsafe_1147_ = lean_ctor_get_uint8(v_val_1141_, sizeof(void*)*6 + 1);
v_type_1148_ = lean_ctor_get(v_toConstantVal_1142_, 2);
v___x_1149_ = l_Lean_Expr_isProp(v_type_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = l_Lean_InductiveVal_numTypeFormers(v_val_1141_);
lean_dec_ref(v_val_1141_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_dec_eq(v___x_1150_, v___x_1151_);
lean_dec(v___x_1150_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v_ctors_1145_);
lean_dec(v_numIndices_1144_);
lean_dec(v_numParams_1143_);
v___x_1153_ = lean_box(v___x_1152_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1153_);
v___x_1155_ = v___x_1139_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
else
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_nat_dec_eq(v_numIndices_1144_, v___x_1157_);
lean_dec(v_numIndices_1144_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec(v_ctors_1145_);
lean_dec(v_numParams_1143_);
v___x_1159_ = lean_box(v___x_1158_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1159_);
v___x_1161_ = v___x_1139_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_nat_dec_eq(v_numParams_1143_, v___x_1157_);
lean_dec(v_numParams_1143_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v_ctors_1145_);
v___x_1164_ = lean_box(v___x_1163_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1164_);
v___x_1166_ = v___x_1139_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = l_List_isEmpty___redArg(v_ctors_1145_);
if (v___x_1168_ == 0)
{
if (v_isRec_1146_ == 0)
{
if (v_isUnsafe_1147_ == 0)
{
lean_object* v___x_1169_; 
lean_del_object(v___x_1139_);
v___x_1169_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_1147_, v_ctors_1145_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
lean_dec(v_ctors_1145_);
v___x_1170_ = lean_box(v_isRec_1146_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1170_);
v___x_1172_ = v___x_1139_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_dec(v_ctors_1145_);
v___x_1174_ = lean_box(v___x_1168_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1174_);
v___x_1176_ = v___x_1139_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
lean_dec(v_ctors_1145_);
v___x_1178_ = lean_box(v___x_1149_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1178_);
v___x_1180_ = v___x_1139_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
else
{
uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_ctors_1145_);
lean_dec(v_numIndices_1144_);
lean_dec(v_numParams_1143_);
lean_dec_ref(v_val_1141_);
v___x_1182_ = 0;
v___x_1183_ = lean_box(v___x_1182_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1183_);
v___x_1185_ = v___x_1139_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_dec(v_a_1137_);
v___x_1187_ = 0;
v___x_1188_ = lean_box(v___x_1187_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1188_);
v___x_1190_ = v___x_1139_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1136_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1136_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object* v_declName_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_declName_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
v___x_1215_ = lean_apply_6(v_k_1208_, v_b_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, lean_box(0));
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1216_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1224_, uint8_t v_bi_1225_, lean_object* v_type_1226_, lean_object* v_k_1227_, uint8_t v_kind_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___f_1234_; lean_object* v___x_1235_; 
v___f_1234_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1234_, 0, v_k_1227_);
v___x_1235_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1224_, v_bi_1225_, v_type_1226_, v___f_1234_, v_kind_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_a_1244_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1235_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1235_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1252_, lean_object* v_bi_1253_, lean_object* v_type_1254_, lean_object* v_k_1255_, lean_object* v_kind_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v_bi_boxed_1262_; uint8_t v_kind_boxed_1263_; lean_object* v_res_1264_; 
v_bi_boxed_1262_ = lean_unbox(v_bi_1253_);
v_kind_boxed_1263_ = lean_unbox(v_kind_1256_);
v_res_1264_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1252_, v_bi_boxed_1262_, v_type_1254_, v_k_1255_, v_kind_boxed_1263_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object* v_name_1265_, lean_object* v_type_1266_, lean_object* v_k_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = 0;
v___x_1274_ = 0;
v___x_1275_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1265_, v___x_1273_, v_type_1266_, v_k_1267_, v___x_1274_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1276_, lean_object* v_type_1277_, lean_object* v_k_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_1276_, v_type_1277_, v_k_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v_nextMacroScope_1290_; lean_object* v_ngen_1291_; lean_object* v_auxDeclNGen_1292_; lean_object* v_traceState_1293_; lean_object* v_messages_1294_; lean_object* v_infoState_1295_; lean_object* v_snapshotTasks_1296_; lean_object* v_newDecls_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1323_; 
v___x_1289_ = lean_st_ref_take(v___y_1287_);
v_nextMacroScope_1290_ = lean_ctor_get(v___x_1289_, 1);
v_ngen_1291_ = lean_ctor_get(v___x_1289_, 2);
v_auxDeclNGen_1292_ = lean_ctor_get(v___x_1289_, 3);
v_traceState_1293_ = lean_ctor_get(v___x_1289_, 4);
v_messages_1294_ = lean_ctor_get(v___x_1289_, 6);
v_infoState_1295_ = lean_ctor_get(v___x_1289_, 7);
v_snapshotTasks_1296_ = lean_ctor_get(v___x_1289_, 8);
v_newDecls_1297_ = lean_ctor_get(v___x_1289_, 9);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1324_ = lean_ctor_get(v___x_1289_, 5);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v___x_1289_, 0);
lean_dec(v_unused_1325_);
v___x_1299_ = v___x_1289_;
v_isShared_1300_ = v_isSharedCheck_1323_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_newDecls_1297_);
lean_inc(v_snapshotTasks_1296_);
lean_inc(v_infoState_1295_);
lean_inc(v_messages_1294_);
lean_inc(v_traceState_1293_);
lean_inc(v_auxDeclNGen_1292_);
lean_inc(v_ngen_1291_);
lean_inc(v_nextMacroScope_1290_);
lean_dec(v___x_1289_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1323_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 5, v___x_1301_);
lean_ctor_set(v___x_1299_, 0, v_env_1285_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_env_1285_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_nextMacroScope_1290_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_ngen_1291_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_auxDeclNGen_1292_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_traceState_1293_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v_messages_1294_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_infoState_1295_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v_snapshotTasks_1296_);
lean_ctor_set(v_reuseFailAlloc_1322_, 9, v_newDecls_1297_);
v___x_1303_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_mctx_1306_; lean_object* v_zetaDeltaFVarIds_1307_; lean_object* v_postponed_1308_; lean_object* v_diag_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1320_; 
v___x_1304_ = lean_st_ref_set(v___y_1287_, v___x_1303_);
v___x_1305_ = lean_st_ref_take(v___y_1286_);
v_mctx_1306_ = lean_ctor_get(v___x_1305_, 0);
v_zetaDeltaFVarIds_1307_ = lean_ctor_get(v___x_1305_, 2);
v_postponed_1308_ = lean_ctor_get(v___x_1305_, 3);
v_diag_1309_ = lean_ctor_get(v___x_1305_, 4);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1305_, 1);
lean_dec(v_unused_1321_);
v___x_1311_ = v___x_1305_;
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_diag_1309_);
lean_inc(v_postponed_1308_);
lean_inc(v_zetaDeltaFVarIds_1307_);
lean_inc(v_mctx_1306_);
lean_dec(v___x_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_mctx_1306_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_zetaDeltaFVarIds_1307_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_postponed_1308_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_diag_1309_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_st_ref_set(v___y_1286_, v___x_1315_);
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object* v_declName_1331_, lean_object* v_entry_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; lean_object* v_env_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1338_ = lean_st_ref_get(v___y_1336_);
v_env_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc_ref(v_env_1339_);
lean_dec(v___x_1338_);
v___x_1340_ = l_Lean_Linter_deprecatedAttr;
v___x_1341_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1340_, v_env_1339_, v_declName_1331_, v_entry_1332_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1351_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 3);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = l_Lean_MessageData_ofFormat(v___x_1347_);
v___x_1349_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_1348_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1352_);
lean_dec_ref(v___x_1341_);
v___x_1353_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_1352_, v___y_1334_, v___y_1336_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object* v_declName_1354_, lean_object* v_entry_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v_declName_1354_, v_entry_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_1362_, uint8_t v_s_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; lean_object* v_env_1368_; lean_object* v_nextMacroScope_1369_; lean_object* v_ngen_1370_; lean_object* v_auxDeclNGen_1371_; lean_object* v_traceState_1372_; lean_object* v_messages_1373_; lean_object* v_infoState_1374_; lean_object* v_snapshotTasks_1375_; lean_object* v_newDecls_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1405_; 
v___x_1367_ = lean_st_ref_take(v___y_1365_);
v_env_1368_ = lean_ctor_get(v___x_1367_, 0);
v_nextMacroScope_1369_ = lean_ctor_get(v___x_1367_, 1);
v_ngen_1370_ = lean_ctor_get(v___x_1367_, 2);
v_auxDeclNGen_1371_ = lean_ctor_get(v___x_1367_, 3);
v_traceState_1372_ = lean_ctor_get(v___x_1367_, 4);
v_messages_1373_ = lean_ctor_get(v___x_1367_, 6);
v_infoState_1374_ = lean_ctor_get(v___x_1367_, 7);
v_snapshotTasks_1375_ = lean_ctor_get(v___x_1367_, 8);
v_newDecls_1376_ = lean_ctor_get(v___x_1367_, 9);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1367_, 5);
lean_dec(v_unused_1406_);
v___x_1378_ = v___x_1367_;
v_isShared_1379_ = v_isSharedCheck_1405_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_newDecls_1376_);
lean_inc(v_snapshotTasks_1375_);
lean_inc(v_infoState_1374_);
lean_inc(v_messages_1373_);
lean_inc(v_traceState_1372_);
lean_inc(v_auxDeclNGen_1371_);
lean_inc(v_ngen_1370_);
lean_inc(v_nextMacroScope_1369_);
lean_inc(v_env_1368_);
lean_dec(v___x_1367_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1405_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1380_ = 0;
v___x_1381_ = lean_box(0);
v___x_1382_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1368_, v_declName_1362_, v_s_1363_, v___x_1380_, v___x_1381_);
v___x_1383_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 5, v___x_1383_);
lean_ctor_set(v___x_1378_, 0, v___x_1382_);
v___x_1385_ = v___x_1378_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_nextMacroScope_1369_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_ngen_1370_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_auxDeclNGen_1371_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_traceState_1372_);
lean_ctor_set(v_reuseFailAlloc_1404_, 5, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1404_, 6, v_messages_1373_);
lean_ctor_set(v_reuseFailAlloc_1404_, 7, v_infoState_1374_);
lean_ctor_set(v_reuseFailAlloc_1404_, 8, v_snapshotTasks_1375_);
lean_ctor_set(v_reuseFailAlloc_1404_, 9, v_newDecls_1376_);
v___x_1385_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_mctx_1388_; lean_object* v_zetaDeltaFVarIds_1389_; lean_object* v_postponed_1390_; lean_object* v_diag_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1402_; 
v___x_1386_ = lean_st_ref_set(v___y_1365_, v___x_1385_);
v___x_1387_ = lean_st_ref_take(v___y_1364_);
v_mctx_1388_ = lean_ctor_get(v___x_1387_, 0);
v_zetaDeltaFVarIds_1389_ = lean_ctor_get(v___x_1387_, 2);
v_postponed_1390_ = lean_ctor_get(v___x_1387_, 3);
v_diag_1391_ = lean_ctor_get(v___x_1387_, 4);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1387_, 1);
lean_dec(v_unused_1403_);
v___x_1393_ = v___x_1387_;
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_diag_1391_);
lean_inc(v_postponed_1390_);
lean_inc(v_zetaDeltaFVarIds_1389_);
lean_inc(v_mctx_1388_);
lean_dec(v___x_1387_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_mctx_1388_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_zetaDeltaFVarIds_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_postponed_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_diag_1391_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_st_ref_set(v___y_1364_, v___x_1397_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_1407_, lean_object* v_s_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_s_boxed_1412_; lean_object* v_res_1413_; 
v_s_boxed_1412_ = lean_unbox(v_s_1408_);
v_res_1413_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1407_, v_s_boxed_1412_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec(v___y_1409_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object* v_declName_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = 0;
v___x_1421_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1414_, v___x_1420_, v___y_1416_, v___y_1418_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object* v_declName_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v_declName_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object* v___x_1435_, lean_object* v___x_1436_, lean_object* v_xs_1437_, uint8_t v___x_1438_, uint8_t v___x_1439_, lean_object* v_val_1440_, lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v_ctors_1445_, lean_object* v___x_1446_, lean_object* v___x_1447_, lean_object* v_levelParams_1448_, lean_object* v_indName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___x_1548_; 
lean_inc_ref(v___x_1436_);
lean_inc_ref(v___x_1435_);
v___x_1548_ = l_Lean_mkArrow(v___x_1435_, v___x_1436_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = 1;
v___x_1551_ = l_Lean_Meta_mkForallFVars(v_xs_1437_, v_a_1549_, v___x_1438_, v___x_1439_, v___x_1439_, v___x_1550_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = lean_box(v___x_1438_);
v___x_1554_ = lean_box(v___x_1439_);
v___x_1555_ = lean_box(v___x_1550_);
lean_inc(v___x_1442_);
lean_inc_ref(v_val_1440_);
v___f_1556_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1556_, 0, v_xs_1437_);
lean_closure_set(v___f_1556_, 1, v___x_1553_);
lean_closure_set(v___f_1556_, 2, v___x_1554_);
lean_closure_set(v___f_1556_, 3, v___x_1555_);
lean_closure_set(v___f_1556_, 4, v_val_1440_);
lean_closure_set(v___f_1556_, 5, v___x_1441_);
lean_closure_set(v___f_1556_, 6, v___x_1436_);
lean_closure_set(v___f_1556_, 7, v___x_1442_);
lean_closure_set(v___f_1556_, 8, v___x_1443_);
lean_closure_set(v___f_1556_, 9, v___x_1444_);
lean_closure_set(v___f_1556_, 10, v_ctors_1445_);
lean_closure_set(v___f_1556_, 11, v___x_1446_);
v___x_1557_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__3));
v___x_1558_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v___x_1557_, v___x_1435_, v___f_1556_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; lean_object* v_env_1561_; uint32_t v___x_1562_; uint32_t v___x_1563_; uint32_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1772_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc_n(v_a_1559_, 2);
lean_dec_ref(v___x_1558_);
v___x_1560_ = lean_st_ref_get(v___y_1453_);
v_env_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_env_1561_);
lean_dec(v___x_1560_);
v___x_1562_ = l_Lean_getMaxHeight(v_env_1561_, v_a_1559_);
v___x_1563_ = 1;
v___x_1564_ = lean_uint32_add(v___x_1562_, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1565_, 0, v___x_1564_);
lean_inc(v_a_1552_);
lean_inc(v_levelParams_1448_);
lean_inc(v___x_1447_);
v___x_1566_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1447_, v_levelParams_1448_, v_a_1552_, v_a_1559_, v___x_1565_, v___y_1453_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1772_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1772_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 1);
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___x_1695_; 
lean_inc_ref(v___x_1572_);
v___x_1695_ = l_Lean_addDecl(v___x_1572_, v___x_1438_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v___x_1696_; lean_object* v_env_1697_; lean_object* v_nextMacroScope_1698_; lean_object* v_ngen_1699_; lean_object* v_auxDeclNGen_1700_; lean_object* v_traceState_1701_; lean_object* v_messages_1702_; lean_object* v_infoState_1703_; lean_object* v_snapshotTasks_1704_; lean_object* v_newDecls_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v___x_1695_);
v___x_1696_ = lean_st_ref_take(v___y_1453_);
v_env_1697_ = lean_ctor_get(v___x_1696_, 0);
v_nextMacroScope_1698_ = lean_ctor_get(v___x_1696_, 1);
v_ngen_1699_ = lean_ctor_get(v___x_1696_, 2);
v_auxDeclNGen_1700_ = lean_ctor_get(v___x_1696_, 3);
v_traceState_1701_ = lean_ctor_get(v___x_1696_, 4);
v_messages_1702_ = lean_ctor_get(v___x_1696_, 6);
v_infoState_1703_ = lean_ctor_get(v___x_1696_, 7);
v_snapshotTasks_1704_ = lean_ctor_get(v___x_1696_, 8);
v_newDecls_1705_ = lean_ctor_get(v___x_1696_, 9);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1696_, 5);
lean_dec(v_unused_1770_);
v___x_1707_ = v___x_1696_;
v_isShared_1708_ = v_isSharedCheck_1769_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_newDecls_1705_);
lean_inc(v_snapshotTasks_1704_);
lean_inc(v_infoState_1703_);
lean_inc(v_messages_1702_);
lean_inc(v_traceState_1701_);
lean_inc(v_auxDeclNGen_1700_);
lean_inc(v_ngen_1699_);
lean_inc(v_nextMacroScope_1698_);
lean_inc(v_env_1697_);
lean_dec(v___x_1696_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1769_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_inc(v___x_1447_);
v___x_1709_ = l_Lean_Meta_addToCompletionBlackList(v_env_1697_, v___x_1447_);
v___x_1710_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 5, v___x_1710_);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_nextMacroScope_1698_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_ngen_1699_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_auxDeclNGen_1700_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_traceState_1701_);
lean_ctor_set(v_reuseFailAlloc_1768_, 5, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1768_, 6, v_messages_1702_);
lean_ctor_set(v_reuseFailAlloc_1768_, 7, v_infoState_1703_);
lean_ctor_set(v_reuseFailAlloc_1768_, 8, v_snapshotTasks_1704_);
lean_ctor_set(v_reuseFailAlloc_1768_, 9, v_newDecls_1705_);
v___x_1712_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v_mctx_1715_; lean_object* v_zetaDeltaFVarIds_1716_; lean_object* v_postponed_1717_; lean_object* v_diag_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1766_; 
v___x_1713_ = lean_st_ref_set(v___y_1453_, v___x_1712_);
v___x_1714_ = lean_st_ref_take(v___y_1451_);
v_mctx_1715_ = lean_ctor_get(v___x_1714_, 0);
v_zetaDeltaFVarIds_1716_ = lean_ctor_get(v___x_1714_, 2);
v_postponed_1717_ = lean_ctor_get(v___x_1714_, 3);
v_diag_1718_ = lean_ctor_get(v___x_1714_, 4);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1714_, 1);
lean_dec(v_unused_1767_);
v___x_1720_ = v___x_1714_;
v_isShared_1721_ = v_isSharedCheck_1766_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_diag_1718_);
lean_inc(v_postponed_1717_);
lean_inc(v_zetaDeltaFVarIds_1716_);
lean_inc(v_mctx_1715_);
lean_dec(v___x_1714_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1766_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_mctx_1715_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_zetaDeltaFVarIds_1716_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_postponed_1717_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_diag_1718_);
v___x_1724_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_env_1727_; lean_object* v_nextMacroScope_1728_; lean_object* v_ngen_1729_; lean_object* v_auxDeclNGen_1730_; lean_object* v_traceState_1731_; lean_object* v_messages_1732_; lean_object* v_infoState_1733_; lean_object* v_snapshotTasks_1734_; lean_object* v_newDecls_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1763_; 
v___x_1725_ = lean_st_ref_set(v___y_1451_, v___x_1724_);
v___x_1726_ = lean_st_ref_take(v___y_1453_);
v_env_1727_ = lean_ctor_get(v___x_1726_, 0);
v_nextMacroScope_1728_ = lean_ctor_get(v___x_1726_, 1);
v_ngen_1729_ = lean_ctor_get(v___x_1726_, 2);
v_auxDeclNGen_1730_ = lean_ctor_get(v___x_1726_, 3);
v_traceState_1731_ = lean_ctor_get(v___x_1726_, 4);
v_messages_1732_ = lean_ctor_get(v___x_1726_, 6);
v_infoState_1733_ = lean_ctor_get(v___x_1726_, 7);
v_snapshotTasks_1734_ = lean_ctor_get(v___x_1726_, 8);
v_newDecls_1735_ = lean_ctor_get(v___x_1726_, 9);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v___x_1726_, 5);
lean_dec(v_unused_1764_);
v___x_1737_ = v___x_1726_;
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_newDecls_1735_);
lean_inc(v_snapshotTasks_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_traceState_1731_);
lean_inc(v_auxDeclNGen_1730_);
lean_inc(v_ngen_1729_);
lean_inc(v_nextMacroScope_1728_);
lean_inc(v_env_1727_);
lean_dec(v___x_1726_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_inc(v___x_1447_);
v___x_1739_ = l_Lean_addProtected(v_env_1727_, v___x_1447_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 5, v___x_1710_);
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_nextMacroScope_1728_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_ngen_1729_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_auxDeclNGen_1730_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_traceState_1731_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_messages_1732_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_infoState_1733_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_snapshotTasks_1734_);
lean_ctor_set(v_reuseFailAlloc_1762_, 9, v_newDecls_1735_);
v___x_1741_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_mctx_1744_; lean_object* v_zetaDeltaFVarIds_1745_; lean_object* v_postponed_1746_; lean_object* v_diag_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1760_; 
v___x_1742_ = lean_st_ref_set(v___y_1453_, v___x_1741_);
v___x_1743_ = lean_st_ref_take(v___y_1451_);
v_mctx_1744_ = lean_ctor_get(v___x_1743_, 0);
v_zetaDeltaFVarIds_1745_ = lean_ctor_get(v___x_1743_, 2);
v_postponed_1746_ = lean_ctor_get(v___x_1743_, 3);
v_diag_1747_ = lean_ctor_get(v___x_1743_, 4);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1743_, 1);
lean_dec(v_unused_1761_);
v___x_1749_ = v___x_1743_;
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_diag_1747_);
lean_inc(v_postponed_1746_);
lean_inc(v_zetaDeltaFVarIds_1745_);
lean_inc(v_mctx_1744_);
lean_dec(v___x_1743_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1722_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_mctx_1744_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_zetaDeltaFVarIds_1745_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_postponed_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_diag_1747_);
v___x_1752_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1753_ = lean_st_ref_set(v___y_1451_, v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = l_Lean_InductiveVal_numCtors(v_val_1440_);
lean_dec_ref(v_val_1440_);
v___x_1756_ = lean_nat_dec_eq(v___x_1755_, v___x_1754_);
lean_dec(v___x_1755_);
if (v___x_1756_ == 0)
{
v___y_1652_ = v___y_1450_;
v___y_1653_ = v___y_1451_;
v___y_1654_ = v___y_1452_;
v___y_1655_ = v___y_1453_;
goto v___jp_1651_;
}
else
{
uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = 2;
lean_inc(v___x_1447_);
v___x_1758_ = l_Lean_Meta_setInlineAttribute(v___x_1447_, v___x_1757_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec_ref(v___x_1758_);
v___y_1652_ = v___y_1450_;
v___y_1653_ = v___y_1451_;
v___y_1654_ = v___y_1452_;
v___y_1655_ = v___y_1453_;
goto v___jp_1651_;
}
else
{
lean_dec_ref(v___x_1572_);
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
return v___x_1758_;
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
lean_dec_ref(v___x_1572_);
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
lean_dec_ref(v_val_1440_);
return v___x_1695_;
}
v___jp_1573_:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_compileDecl(v___x_1572_, v___x_1439_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v___x_1578_);
lean_inc(v___x_1447_);
v___x_1579_ = l_Lean_enableRealizationsForConst(v___x_1447_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v___x_1579_);
lean_inc(v_indName_1449_);
v___x_1580_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_indName_1449_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1642_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1642_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1642_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_unbox(v_a_1581_);
lean_dec(v_a_1581_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
v___x_1586_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1641_; 
lean_del_object(v___x_1583_);
lean_inc(v_indName_1449_);
v___x_1590_ = l_mkToCtorIdxName(v_indName_1449_);
lean_inc(v___x_1447_);
v___x_1591_ = l_Lean_mkConst(v___x_1447_, v___x_1442_);
v___x_1592_ = lean_box(1);
lean_inc(v___x_1590_);
v___x_1593_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1590_, v_levelParams_1448_, v_a_1552_, v___x_1591_, v___x_1592_, v___y_1577_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1641_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1641_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 1);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_addDecl(v___x_1599_, v___x_1438_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; lean_object* v_env_1602_; uint8_t v___x_1603_; 
lean_dec_ref(v___x_1600_);
v___x_1601_ = lean_st_ref_get(v___y_1577_);
v_env_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_env_1602_);
lean_dec(v___x_1601_);
v___x_1603_ = l_Lean_isMarkedMeta(v_env_1602_, v_indName_1449_);
if (v___x_1603_ == 0)
{
v___y_1456_ = v___x_1590_;
v___y_1457_ = v___y_1574_;
v___y_1458_ = v___y_1575_;
v___y_1459_ = v___y_1576_;
v___y_1460_ = v___y_1577_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_traceState_1609_; lean_object* v_messages_1610_; lean_object* v_infoState_1611_; lean_object* v_snapshotTasks_1612_; lean_object* v_newDecls_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1638_; 
v___x_1604_ = lean_st_ref_take(v___y_1577_);
v_env_1605_ = lean_ctor_get(v___x_1604_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1604_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1604_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1604_, 3);
v_traceState_1609_ = lean_ctor_get(v___x_1604_, 4);
v_messages_1610_ = lean_ctor_get(v___x_1604_, 6);
v_infoState_1611_ = lean_ctor_get(v___x_1604_, 7);
v_snapshotTasks_1612_ = lean_ctor_get(v___x_1604_, 8);
v_newDecls_1613_ = lean_ctor_get(v___x_1604_, 9);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v___x_1604_, 5);
lean_dec(v_unused_1639_);
v___x_1615_ = v___x_1604_;
v_isShared_1616_ = v_isSharedCheck_1638_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_newDecls_1613_);
lean_inc(v_snapshotTasks_1612_);
lean_inc(v_infoState_1611_);
lean_inc(v_messages_1610_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1604_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1638_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
lean_inc(v___x_1590_);
v___x_1617_ = l_Lean_markMeta(v_env_1605_, v___x_1590_);
v___x_1618_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 5, v___x_1618_);
lean_ctor_set(v___x_1615_, 0, v___x_1617_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_traceState_1609_);
lean_ctor_set(v_reuseFailAlloc_1637_, 5, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1637_, 6, v_messages_1610_);
lean_ctor_set(v_reuseFailAlloc_1637_, 7, v_infoState_1611_);
lean_ctor_set(v_reuseFailAlloc_1637_, 8, v_snapshotTasks_1612_);
lean_ctor_set(v_reuseFailAlloc_1637_, 9, v_newDecls_1613_);
v___x_1620_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_mctx_1623_; lean_object* v_zetaDeltaFVarIds_1624_; lean_object* v_postponed_1625_; lean_object* v_diag_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1635_; 
v___x_1621_ = lean_st_ref_set(v___y_1577_, v___x_1620_);
v___x_1622_ = lean_st_ref_take(v___y_1575_);
v_mctx_1623_ = lean_ctor_get(v___x_1622_, 0);
v_zetaDeltaFVarIds_1624_ = lean_ctor_get(v___x_1622_, 2);
v_postponed_1625_ = lean_ctor_get(v___x_1622_, 3);
v_diag_1626_ = lean_ctor_get(v___x_1622_, 4);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; 
v_unused_1636_ = lean_ctor_get(v___x_1622_, 1);
lean_dec(v_unused_1636_);
v___x_1628_ = v___x_1622_;
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_diag_1626_);
lean_inc(v_postponed_1625_);
lean_inc(v_zetaDeltaFVarIds_1624_);
lean_inc(v_mctx_1623_);
lean_dec(v___x_1622_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 1, v___x_1630_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_mctx_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_zetaDeltaFVarIds_1624_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_postponed_1625_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_diag_1626_);
v___x_1632_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_st_ref_set(v___y_1575_, v___x_1632_);
v___y_1456_ = v___x_1590_;
v___y_1457_ = v___y_1574_;
v___y_1458_ = v___y_1575_;
v___y_1459_ = v___y_1576_;
v___y_1460_ = v___y_1577_;
goto v___jp_1455_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1590_);
lean_dec(v_indName_1449_);
lean_dec(v___x_1447_);
return v___x_1600_;
}
}
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
v_a_1643_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1580_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1580_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
return v___x_1579_;
}
}
else
{
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
return v___x_1578_;
}
}
v___jp_1651_:
{
lean_object* v___x_1656_; lean_object* v_env_1657_; uint8_t v___x_1658_; 
v___x_1656_ = lean_st_ref_get(v___y_1655_);
v_env_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc_ref(v_env_1657_);
lean_dec(v___x_1656_);
lean_inc(v_indName_1449_);
v___x_1658_ = l_Lean_isMarkedMeta(v_env_1657_, v_indName_1449_);
if (v___x_1658_ == 0)
{
v___y_1574_ = v___y_1652_;
v___y_1575_ = v___y_1653_;
v___y_1576_ = v___y_1654_;
v___y_1577_ = v___y_1655_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1659_; lean_object* v_env_1660_; lean_object* v_nextMacroScope_1661_; lean_object* v_ngen_1662_; lean_object* v_auxDeclNGen_1663_; lean_object* v_traceState_1664_; lean_object* v_messages_1665_; lean_object* v_infoState_1666_; lean_object* v_snapshotTasks_1667_; lean_object* v_newDecls_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1693_; 
v___x_1659_ = lean_st_ref_take(v___y_1655_);
v_env_1660_ = lean_ctor_get(v___x_1659_, 0);
v_nextMacroScope_1661_ = lean_ctor_get(v___x_1659_, 1);
v_ngen_1662_ = lean_ctor_get(v___x_1659_, 2);
v_auxDeclNGen_1663_ = lean_ctor_get(v___x_1659_, 3);
v_traceState_1664_ = lean_ctor_get(v___x_1659_, 4);
v_messages_1665_ = lean_ctor_get(v___x_1659_, 6);
v_infoState_1666_ = lean_ctor_get(v___x_1659_, 7);
v_snapshotTasks_1667_ = lean_ctor_get(v___x_1659_, 8);
v_newDecls_1668_ = lean_ctor_get(v___x_1659_, 9);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1659_, 5);
lean_dec(v_unused_1694_);
v___x_1670_ = v___x_1659_;
v_isShared_1671_ = v_isSharedCheck_1693_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_newDecls_1668_);
lean_inc(v_snapshotTasks_1667_);
lean_inc(v_infoState_1666_);
lean_inc(v_messages_1665_);
lean_inc(v_traceState_1664_);
lean_inc(v_auxDeclNGen_1663_);
lean_inc(v_ngen_1662_);
lean_inc(v_nextMacroScope_1661_);
lean_inc(v_env_1660_);
lean_dec(v___x_1659_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1693_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_inc(v___x_1447_);
v___x_1672_ = l_Lean_markMeta(v_env_1660_, v___x_1447_);
v___x_1673_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 5, v___x_1673_);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_nextMacroScope_1661_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_ngen_1662_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_auxDeclNGen_1663_);
lean_ctor_set(v_reuseFailAlloc_1692_, 4, v_traceState_1664_);
lean_ctor_set(v_reuseFailAlloc_1692_, 5, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1692_, 6, v_messages_1665_);
lean_ctor_set(v_reuseFailAlloc_1692_, 7, v_infoState_1666_);
lean_ctor_set(v_reuseFailAlloc_1692_, 8, v_snapshotTasks_1667_);
lean_ctor_set(v_reuseFailAlloc_1692_, 9, v_newDecls_1668_);
v___x_1675_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v_mctx_1678_; lean_object* v_zetaDeltaFVarIds_1679_; lean_object* v_postponed_1680_; lean_object* v_diag_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1690_; 
v___x_1676_ = lean_st_ref_set(v___y_1655_, v___x_1675_);
v___x_1677_ = lean_st_ref_take(v___y_1653_);
v_mctx_1678_ = lean_ctor_get(v___x_1677_, 0);
v_zetaDeltaFVarIds_1679_ = lean_ctor_get(v___x_1677_, 2);
v_postponed_1680_ = lean_ctor_get(v___x_1677_, 3);
v_diag_1681_ = lean_ctor_get(v___x_1677_, 4);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1677_, 1);
lean_dec(v_unused_1691_);
v___x_1683_ = v___x_1677_;
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_diag_1681_);
lean_inc(v_postponed_1680_);
lean_inc(v_zetaDeltaFVarIds_1679_);
lean_inc(v_mctx_1678_);
lean_dec(v___x_1677_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_mctx_1678_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_zetaDeltaFVarIds_1679_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_postponed_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_diag_1681_);
v___x_1687_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_st_ref_set(v___y_1653_, v___x_1687_);
v___y_1574_ = v___y_1652_;
v___y_1575_ = v___y_1653_;
v___y_1576_ = v___y_1654_;
v___y_1577_ = v___y_1655_;
goto v___jp_1573_;
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
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1552_);
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1442_);
lean_dec_ref(v_val_1440_);
v_a_1773_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1558_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1558_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1446_);
lean_dec(v_ctors_1445_);
lean_dec_ref(v___x_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_val_1440_);
lean_dec_ref(v_xs_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
v_a_1781_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1551_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1551_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_indName_1449_);
lean_dec(v_levelParams_1448_);
lean_dec(v___x_1447_);
lean_dec(v___x_1446_);
lean_dec(v_ctors_1445_);
lean_dec_ref(v___x_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v_val_1440_);
lean_dec_ref(v_xs_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
v_a_1789_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1548_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1548_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
v___jp_1455_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
lean_inc(v___y_1456_);
v___x_1463_ = lean_array_push(v___x_1462_, v___y_1456_);
v___x_1464_ = l_Lean_compileDecls(v___x_1463_, v___x_1439_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; lean_object* v_env_1466_; lean_object* v_nextMacroScope_1467_; lean_object* v_ngen_1468_; lean_object* v_auxDeclNGen_1469_; lean_object* v_traceState_1470_; lean_object* v_messages_1471_; lean_object* v_infoState_1472_; lean_object* v_snapshotTasks_1473_; lean_object* v_newDecls_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___x_1464_);
v___x_1465_ = lean_st_ref_take(v___y_1460_);
v_env_1466_ = lean_ctor_get(v___x_1465_, 0);
v_nextMacroScope_1467_ = lean_ctor_get(v___x_1465_, 1);
v_ngen_1468_ = lean_ctor_get(v___x_1465_, 2);
v_auxDeclNGen_1469_ = lean_ctor_get(v___x_1465_, 3);
v_traceState_1470_ = lean_ctor_get(v___x_1465_, 4);
v_messages_1471_ = lean_ctor_get(v___x_1465_, 6);
v_infoState_1472_ = lean_ctor_get(v___x_1465_, 7);
v_snapshotTasks_1473_ = lean_ctor_get(v___x_1465_, 8);
v_newDecls_1474_ = lean_ctor_get(v___x_1465_, 9);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1465_, 5);
lean_dec(v_unused_1547_);
v___x_1476_ = v___x_1465_;
v_isShared_1477_ = v_isSharedCheck_1546_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_newDecls_1474_);
lean_inc(v_snapshotTasks_1473_);
lean_inc(v_infoState_1472_);
lean_inc(v_messages_1471_);
lean_inc(v_traceState_1470_);
lean_inc(v_auxDeclNGen_1469_);
lean_inc(v_ngen_1468_);
lean_inc(v_nextMacroScope_1467_);
lean_inc(v_env_1466_);
lean_dec(v___x_1465_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1546_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_inc(v___y_1456_);
v___x_1478_ = l_Lean_Meta_addToCompletionBlackList(v_env_1466_, v___y_1456_);
v___x_1479_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 5, v___x_1479_);
lean_ctor_set(v___x_1476_, 0, v___x_1478_);
v___x_1481_ = v___x_1476_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_nextMacroScope_1467_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_ngen_1468_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_auxDeclNGen_1469_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_traceState_1470_);
lean_ctor_set(v_reuseFailAlloc_1545_, 5, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1545_, 6, v_messages_1471_);
lean_ctor_set(v_reuseFailAlloc_1545_, 7, v_infoState_1472_);
lean_ctor_set(v_reuseFailAlloc_1545_, 8, v_snapshotTasks_1473_);
lean_ctor_set(v_reuseFailAlloc_1545_, 9, v_newDecls_1474_);
v___x_1481_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_mctx_1484_; lean_object* v_zetaDeltaFVarIds_1485_; lean_object* v_postponed_1486_; lean_object* v_diag_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1543_; 
v___x_1482_ = lean_st_ref_set(v___y_1460_, v___x_1481_);
v___x_1483_ = lean_st_ref_take(v___y_1458_);
v_mctx_1484_ = lean_ctor_get(v___x_1483_, 0);
v_zetaDeltaFVarIds_1485_ = lean_ctor_get(v___x_1483_, 2);
v_postponed_1486_ = lean_ctor_get(v___x_1483_, 3);
v_diag_1487_ = lean_ctor_get(v___x_1483_, 4);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1483_, 1);
lean_dec(v_unused_1544_);
v___x_1489_ = v___x_1483_;
v_isShared_1490_ = v_isSharedCheck_1543_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_diag_1487_);
lean_inc(v_postponed_1486_);
lean_inc(v_zetaDeltaFVarIds_1485_);
lean_inc(v_mctx_1484_);
lean_dec(v___x_1483_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1543_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_mctx_1484_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_zetaDeltaFVarIds_1485_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_postponed_1486_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_diag_1487_);
v___x_1493_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_env_1496_; lean_object* v_nextMacroScope_1497_; lean_object* v_ngen_1498_; lean_object* v_auxDeclNGen_1499_; lean_object* v_traceState_1500_; lean_object* v_messages_1501_; lean_object* v_infoState_1502_; lean_object* v_snapshotTasks_1503_; lean_object* v_newDecls_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1540_; 
v___x_1494_ = lean_st_ref_set(v___y_1458_, v___x_1493_);
v___x_1495_ = lean_st_ref_take(v___y_1460_);
v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
v_nextMacroScope_1497_ = lean_ctor_get(v___x_1495_, 1);
v_ngen_1498_ = lean_ctor_get(v___x_1495_, 2);
v_auxDeclNGen_1499_ = lean_ctor_get(v___x_1495_, 3);
v_traceState_1500_ = lean_ctor_get(v___x_1495_, 4);
v_messages_1501_ = lean_ctor_get(v___x_1495_, 6);
v_infoState_1502_ = lean_ctor_get(v___x_1495_, 7);
v_snapshotTasks_1503_ = lean_ctor_get(v___x_1495_, 8);
v_newDecls_1504_ = lean_ctor_get(v___x_1495_, 9);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v___x_1495_, 5);
lean_dec(v_unused_1541_);
v___x_1506_ = v___x_1495_;
v_isShared_1507_ = v_isSharedCheck_1540_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_newDecls_1504_);
lean_inc(v_snapshotTasks_1503_);
lean_inc(v_infoState_1502_);
lean_inc(v_messages_1501_);
lean_inc(v_traceState_1500_);
lean_inc(v_auxDeclNGen_1499_);
lean_inc(v_ngen_1498_);
lean_inc(v_nextMacroScope_1497_);
lean_inc(v_env_1496_);
lean_dec(v___x_1495_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1540_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_inc(v___y_1456_);
v___x_1508_ = l_Lean_addProtected(v_env_1496_, v___y_1456_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 5, v___x_1479_);
lean_ctor_set(v___x_1506_, 0, v___x_1508_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_nextMacroScope_1497_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_ngen_1498_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_auxDeclNGen_1499_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_traceState_1500_);
lean_ctor_set(v_reuseFailAlloc_1539_, 5, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1539_, 6, v_messages_1501_);
lean_ctor_set(v_reuseFailAlloc_1539_, 7, v_infoState_1502_);
lean_ctor_set(v_reuseFailAlloc_1539_, 8, v_snapshotTasks_1503_);
lean_ctor_set(v_reuseFailAlloc_1539_, 9, v_newDecls_1504_);
v___x_1510_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_mctx_1513_; lean_object* v_zetaDeltaFVarIds_1514_; lean_object* v_postponed_1515_; lean_object* v_diag_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1537_; 
v___x_1511_ = lean_st_ref_set(v___y_1460_, v___x_1510_);
v___x_1512_ = lean_st_ref_take(v___y_1458_);
v_mctx_1513_ = lean_ctor_get(v___x_1512_, 0);
v_zetaDeltaFVarIds_1514_ = lean_ctor_get(v___x_1512_, 2);
v_postponed_1515_ = lean_ctor_get(v___x_1512_, 3);
v_diag_1516_ = lean_ctor_get(v___x_1512_, 4);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1512_, 1);
lean_dec(v_unused_1538_);
v___x_1518_ = v___x_1512_;
v_isShared_1519_ = v_isSharedCheck_1537_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_diag_1516_);
lean_inc(v_postponed_1515_);
lean_inc(v_zetaDeltaFVarIds_1514_);
lean_inc(v_mctx_1513_);
lean_dec(v___x_1512_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1537_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1491_);
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_mctx_1513_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_zetaDeltaFVarIds_1514_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_postponed_1515_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_diag_1516_);
v___x_1521_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1534_; 
v___x_1522_ = lean_st_ref_set(v___y_1458_, v___x_1521_);
lean_inc(v___y_1456_);
v___x_1523_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1523_, 0);
lean_dec(v_unused_1535_);
v___x_1525_ = v___x_1523_;
v_isShared_1526_ = v_isSharedCheck_1534_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v___x_1523_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1534_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 1);
lean_ctor_set(v___x_1525_, 0, v___x_1447_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1447_);
v___x_1528_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__1));
v___x_1531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1528_);
lean_ctor_set(v___x_1531_, 1, v___x_1529_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
v___x_1532_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v___y_1456_, v___x_1531_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1532_;
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
lean_dec(v___y_1456_);
lean_dec(v___x_1447_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1797_ = _args[0];
lean_object* v___x_1798_ = _args[1];
lean_object* v_xs_1799_ = _args[2];
lean_object* v___x_1800_ = _args[3];
lean_object* v___x_1801_ = _args[4];
lean_object* v_val_1802_ = _args[5];
lean_object* v___x_1803_ = _args[6];
lean_object* v___x_1804_ = _args[7];
lean_object* v___x_1805_ = _args[8];
lean_object* v___x_1806_ = _args[9];
lean_object* v_ctors_1807_ = _args[10];
lean_object* v___x_1808_ = _args[11];
lean_object* v___x_1809_ = _args[12];
lean_object* v_levelParams_1810_ = _args[13];
lean_object* v_indName_1811_ = _args[14];
lean_object* v___y_1812_ = _args[15];
lean_object* v___y_1813_ = _args[16];
lean_object* v___y_1814_ = _args[17];
lean_object* v___y_1815_ = _args[18];
lean_object* v___y_1816_ = _args[19];
_start:
{
uint8_t v___x_36372__boxed_1817_; uint8_t v___x_36373__boxed_1818_; lean_object* v_res_1819_; 
v___x_36372__boxed_1817_ = lean_unbox(v___x_1800_);
v___x_36373__boxed_1818_ = lean_unbox(v___x_1801_);
v_res_1819_ = l_mkCtorIdx___lam__1(v___x_1797_, v___x_1798_, v_xs_1799_, v___x_36372__boxed_1817_, v___x_36373__boxed_1818_, v_val_1802_, v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v_ctors_1807_, v___x_1808_, v___x_1809_, v_levelParams_1810_, v_indName_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1820_, lean_object* v_k_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1820_, v_k_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1827_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1827_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1844_, lean_object* v_k_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_1844_, v_k_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_bs_1844_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_bs_1854_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1855_ == 0)
{
return v_bs_1854_;
}
else
{
lean_object* v_v_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v_v_1856_ = lean_array_uget(v_bs_1854_, v_i_1853_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1854_, v_i_1853_, v___x_1857_);
v___x_1859_ = l_Lean_Expr_fvarId_x21(v_v_1856_);
lean_dec(v_v_1856_);
v___x_1860_ = 1;
v___x_1861_ = lean_box(v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1859_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1853_, v___x_1863_);
v___x_1865_ = lean_array_uset(v_bs_x27_1858_, v_i_1853_, v___x_1862_);
v_i_1853_ = v___x_1864_;
v_bs_1854_ = v___x_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1867_, lean_object* v_i_1868_, lean_object* v_bs_1869_){
_start:
{
size_t v_sz_boxed_1870_; size_t v_i_boxed_1871_; lean_object* v_res_1872_; 
v_sz_boxed_1870_ = lean_unbox_usize(v_sz_1867_);
lean_dec(v_sz_1867_);
v_i_boxed_1871_ = lean_unbox_usize(v_i_1868_);
lean_dec(v_i_1868_);
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_1870_, v_i_boxed_1871_, v_bs_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object* v_bs_1873_, lean_object* v_k_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
size_t v_sz_1880_; size_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_sz_1880_ = lean_array_size(v_bs_1873_);
v___x_1881_ = ((size_t)0ULL);
v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_1880_, v___x_1881_, v_bs_1873_);
v___x_1883_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_1882_, v_k_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec_ref(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1884_, lean_object* v_k_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_1884_, v_k_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object* v_numParams_1895_, lean_object* v_indName_1896_, lean_object* v___x_1897_, lean_object* v___x_1898_, uint8_t v___x_1899_, uint8_t v___x_1900_, lean_object* v_val_1901_, lean_object* v___x_1902_, lean_object* v_ctors_1903_, lean_object* v___x_1904_, lean_object* v_levelParams_1905_, lean_object* v_xs_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___f_1925_; lean_object* v___x_1926_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1895_);
lean_inc_ref_n(v_xs_1906_, 3);
v___x_1914_ = l_Array_toSubarray___redArg(v_xs_1906_, v___x_1913_, v_numParams_1895_);
v___x_1915_ = l_Subarray_copy___redArg(v___x_1914_);
v___x_1916_ = lean_array_get_size(v_xs_1906_);
v___x_1917_ = l_Array_toSubarray___redArg(v_xs_1906_, v_numParams_1895_, v___x_1916_);
v___x_1918_ = l_Subarray_copy___redArg(v___x_1917_);
lean_inc(v___x_1897_);
lean_inc(v_indName_1896_);
v___x_1919_ = l_Lean_mkConst(v_indName_1896_, v___x_1897_);
v___x_1920_ = l_Lean_mkAppN(v___x_1919_, v_xs_1906_);
v___x_1921_ = ((lean_object*)(l_mkCtorIdx___lam__2___closed__1));
v___x_1922_ = l_Lean_mkConst(v___x_1921_, v___x_1898_);
v___x_1923_ = lean_box(v___x_1899_);
v___x_1924_ = lean_box(v___x_1900_);
v___f_1925_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1925_, 0, v___x_1920_);
lean_closure_set(v___f_1925_, 1, v___x_1922_);
lean_closure_set(v___f_1925_, 2, v_xs_1906_);
lean_closure_set(v___f_1925_, 3, v___x_1923_);
lean_closure_set(v___f_1925_, 4, v___x_1924_);
lean_closure_set(v___f_1925_, 5, v_val_1901_);
lean_closure_set(v___f_1925_, 6, v___x_1918_);
lean_closure_set(v___f_1925_, 7, v___x_1897_);
lean_closure_set(v___f_1925_, 8, v___x_1902_);
lean_closure_set(v___f_1925_, 9, v___x_1915_);
lean_closure_set(v___f_1925_, 10, v_ctors_1903_);
lean_closure_set(v___f_1925_, 11, v___x_1913_);
lean_closure_set(v___f_1925_, 12, v___x_1904_);
lean_closure_set(v___f_1925_, 13, v_levelParams_1905_);
lean_closure_set(v___f_1925_, 14, v_indName_1896_);
v___x_1926_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_xs_1906_, v___f_1925_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1927_ = _args[0];
lean_object* v_indName_1928_ = _args[1];
lean_object* v___x_1929_ = _args[2];
lean_object* v___x_1930_ = _args[3];
lean_object* v___x_1931_ = _args[4];
lean_object* v___x_1932_ = _args[5];
lean_object* v_val_1933_ = _args[6];
lean_object* v___x_1934_ = _args[7];
lean_object* v_ctors_1935_ = _args[8];
lean_object* v___x_1936_ = _args[9];
lean_object* v_levelParams_1937_ = _args[10];
lean_object* v_xs_1938_ = _args[11];
lean_object* v_x_1939_ = _args[12];
lean_object* v___y_1940_ = _args[13];
lean_object* v___y_1941_ = _args[14];
lean_object* v___y_1942_ = _args[15];
lean_object* v___y_1943_ = _args[16];
lean_object* v___y_1944_ = _args[17];
_start:
{
uint8_t v___x_37060__boxed_1945_; uint8_t v___x_37061__boxed_1946_; lean_object* v_res_1947_; 
v___x_37060__boxed_1945_ = lean_unbox(v___x_1931_);
v___x_37061__boxed_1946_ = lean_unbox(v___x_1932_);
v_res_1947_ = l_mkCtorIdx___lam__2(v_numParams_1927_, v_indName_1928_, v___x_1929_, v___x_1930_, v___x_37060__boxed_1945_, v___x_37061__boxed_1946_, v_val_1933_, v___x_1934_, v_ctors_1935_, v___x_1936_, v_levelParams_1937_, v_xs_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v_x_1939_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
if (lean_obj_tag(v_a_1948_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = l_List_reverse___redArg(v_a_1949_);
return v___x_1950_;
}
else
{
lean_object* v_head_1951_; lean_object* v_tail_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1961_; 
v_head_1951_ = lean_ctor_get(v_a_1948_, 0);
v_tail_1952_ = lean_ctor_get(v_a_1948_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1954_ = v_a_1948_;
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_tail_1952_);
lean_inc(v_head_1951_);
lean_dec(v_a_1948_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_mkLevelParam(v_head_1951_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_a_1949_);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_a_1949_);
v___x_1958_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
v_a_1948_ = v_tail_1952_;
v_a_1949_ = v___x_1958_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1964_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_1965_ = lean_unsigned_to_nat(62u);
v___x_1966_ = lean_unsigned_to_nat(48u);
v___x_1967_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__1));
v___x_1968_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__0));
v___x_1969_ = l_mkPanicMessageWithDecl(v___x_1968_, v___x_1967_, v___x_1966_, v___x_1965_, v___x_1964_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object* v_indName_1970_, uint8_t v___x_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_options_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_options_1977_ = lean_ctor_get(v___y_1974_, 2);
v___x_1978_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
v___x_1979_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v_indName_1970_);
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2068_; 
lean_inc(v_indName_1970_);
v___x_1982_ = l_mkCtorIdxName(v_indName_1970_);
lean_inc(v___x_1982_);
v___x_1983_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v___x_1982_, v___x_1979_, v___y_1975_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2068_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2068_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_unbox(v_a_1984_);
lean_dec(v_a_1984_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_del_object(v___x_1986_);
lean_inc(v_indName_1970_);
v___x_1989_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_indName_1970_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v_a_1990_) == 5)
{
lean_object* v_val_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2053_; 
v_val_1991_ = lean_ctor_get(v_a_1990_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_1990_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1993_ = v_a_1990_;
v_isShared_1994_ = v_isSharedCheck_2053_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_val_1991_);
lean_dec(v_a_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2053_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_toConstantVal_1995_; lean_object* v_numParams_1996_; lean_object* v_numIndices_1997_; lean_object* v_ctors_1998_; lean_object* v_levelParams_1999_; lean_object* v_type_2000_; lean_object* v___x_2001_; 
v_toConstantVal_1995_ = lean_ctor_get(v_val_1991_, 0);
v_numParams_1996_ = lean_ctor_get(v_val_1991_, 1);
lean_inc(v_numParams_1996_);
v_numIndices_1997_ = lean_ctor_get(v_val_1991_, 2);
lean_inc(v_numIndices_1997_);
v_ctors_1998_ = lean_ctor_get(v_val_1991_, 4);
lean_inc(v_ctors_1998_);
v_levelParams_1999_ = lean_ctor_get(v_toConstantVal_1995_, 1);
lean_inc(v_levelParams_1999_);
v_type_2000_ = lean_ctor_get(v_toConstantVal_1995_, 2);
lean_inc_ref_n(v_type_2000_, 2);
v___x_2001_ = l_Lean_Meta_isPropFormerType(v_type_2000_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2044_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2044_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2044_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_unbox(v_a_2002_);
lean_dec(v_a_2002_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_del_object(v___x_2004_);
lean_inc(v_indName_1970_);
v___x_2007_ = l_Lean_mkCasesOnName(v_indName_1970_);
lean_inc(v___x_2007_);
v___x_2008_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v___x_2007_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2031_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2031_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2031_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2013_ = l_List_lengthTR___redArg(v_levelParams_1999_);
v___x_2014_ = l_Lean_ConstantInfo_levelParams(v_a_2009_);
lean_dec(v_a_2009_);
v___x_2015_ = l_List_lengthTR___redArg(v___x_2014_);
lean_dec(v___x_2014_);
v___x_2016_ = lean_nat_dec_lt(v___x_2013_, v___x_2015_);
lean_dec(v___x_2015_);
lean_dec(v___x_2013_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_dec(v___x_2007_);
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2017_ = lean_box(0);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2017_);
v___x_2019_ = v___x_2011_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_del_object(v___x_2011_);
v___x_2021_ = lean_box(0);
lean_inc(v_levelParams_1999_);
v___x_2022_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(v_levelParams_1999_, v___x_2021_);
v___x_2023_ = lean_box(v___x_1971_);
v___x_2024_ = lean_box(v___x_1979_);
lean_inc(v_numParams_1996_);
v___f_2025_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2025_, 0, v_numParams_1996_);
lean_closure_set(v___f_2025_, 1, v_indName_1970_);
lean_closure_set(v___f_2025_, 2, v___x_2022_);
lean_closure_set(v___f_2025_, 3, v___x_2021_);
lean_closure_set(v___f_2025_, 4, v___x_2023_);
lean_closure_set(v___f_2025_, 5, v___x_2024_);
lean_closure_set(v___f_2025_, 6, v_val_1991_);
lean_closure_set(v___f_2025_, 7, v___x_2007_);
lean_closure_set(v___f_2025_, 8, v_ctors_1998_);
lean_closure_set(v___f_2025_, 9, v___x_1982_);
lean_closure_set(v___f_2025_, 10, v_levelParams_1999_);
v___x_2026_ = lean_nat_add(v_numParams_1996_, v_numIndices_1997_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 1);
lean_ctor_set(v___x_1993_, 0, v___x_2026_);
v___x_2028_ = v___x_1993_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_2000_, v___x_2028_, v___f_2025_, v___x_1971_, v___x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v___x_2007_);
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v_a_2032_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2008_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2008_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2040_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2040_);
v___x_2042_ = v___x_2004_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v_a_2045_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2001_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2001_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_a_1990_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2054_ = lean_obj_once(&l_mkCtorIdx___lam__3___closed__2, &l_mkCtorIdx___lam__3___closed__2_once, _init_l_mkCtorIdx___lam__3___closed__2);
v___x_2055_ = l_panic___at___00mkCtorIdx_spec__13(v___x_2054_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_2055_;
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v_a_2056_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1989_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1989_);
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
else
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2064_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2064_);
v___x_2066_ = v___x_1986_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2069_, lean_object* v___x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v___x_37173__boxed_2076_; lean_object* v_res_2077_; 
v___x_37173__boxed_2076_ = lean_unbox(v___x_2070_);
v_res_2077_ = l_mkCtorIdx___lam__3(v_indName_2069_, v___x_37173__boxed_2076_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object* v___x_2078_, lean_object* v_e_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = l_Lean_indentD(v_e_2079_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object* v___f_2082_, lean_object* v___f_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2082_, v___f_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2089_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2089_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object* v___f_2106_, lean_object* v___f_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_mkCtorIdx___lam__5(v___f_2106_, v___f_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2113_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_mkCtorIdx___closed__0));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_mkCtorIdx___closed__2));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object* v_indName_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; uint8_t v___x_2136_; 
v___x_2126_ = lean_obj_once(&l_mkCtorIdx___closed__1, &l_mkCtorIdx___closed__1_once, _init_l_mkCtorIdx___closed__1);
v___x_2127_ = 0;
v___x_2128_ = lean_box(v___x_2127_);
lean_inc_n(v_indName_2120_, 2);
v___f_2129_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2129_, 0, v_indName_2120_);
lean_closure_set(v___f_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_MessageData_ofConstName(v_indName_2120_, v___x_2127_);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2126_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_obj_once(&l_mkCtorIdx___closed__3, &l_mkCtorIdx___closed__3_once, _init_l_mkCtorIdx___closed__3);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___f_2134_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2134_, 0, v___x_2133_);
v___f_2135_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2135_, 0, v___f_2129_);
lean_closure_set(v___f_2135_, 1, v___f_2134_);
v___x_2136_ = l_Lean_isPrivateName(v_indName_2120_);
lean_dec(v_indName_2120_);
if (v___x_2136_ == 0)
{
uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = 1;
v___x_2138_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2135_, v___x_2137_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2135_, v___x_2127_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object* v_indName_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_mkCtorIdx(v_indName_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t v___x_2147_, lean_object* v___x_2148_, lean_object* v_as_2149_, lean_object* v_as_x27_2150_, lean_object* v_b_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_2147_, v___x_2148_, v_as_x27_2150_, v_b_2151_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object* v___x_2159_, lean_object* v___x_2160_, lean_object* v_as_2161_, lean_object* v_as_x27_2162_, lean_object* v_b_2163_, lean_object* v_a_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v___x_37480__boxed_2170_; lean_object* v_res_2171_; 
v___x_37480__boxed_2170_ = lean_unbox(v___x_2159_);
v_res_2171_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(v___x_37480__boxed_2170_, v___x_2160_, v_as_2161_, v_as_x27_2162_, v_b_2163_, v_a_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_as_x27_2162_);
lean_dec(v_as_2161_);
lean_dec_ref(v___x_2160_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2172_, lean_object* v_name_2173_, uint8_t v_bi_2174_, lean_object* v_type_2175_, lean_object* v_k_2176_, uint8_t v_kind_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_2173_, v_bi_2174_, v_type_2175_, v_k_2176_, v_kind_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2184_, lean_object* v_name_2185_, lean_object* v_bi_2186_, lean_object* v_type_2187_, lean_object* v_k_2188_, lean_object* v_kind_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v_bi_boxed_2195_; uint8_t v_kind_boxed_2196_; lean_object* v_res_2197_; 
v_bi_boxed_2195_ = lean_unbox(v_bi_2186_);
v_kind_boxed_2196_ = lean_unbox(v_kind_2189_);
v_res_2197_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_2184_, v_name_2185_, v_bi_boxed_2195_, v_type_2187_, v_k_2188_, v_kind_boxed_2196_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object* v_00_u03b1_2198_, lean_object* v_name_2199_, lean_object* v_type_2200_, lean_object* v_k_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_2199_, v_type_2200_, v_k_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_name_2209_, lean_object* v_type_2210_, lean_object* v_k_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(v_00_u03b1_2208_, v_name_2209_, v_type_2210_, v_k_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2218_, uint8_t v_s_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_2218_, v_s_2219_, v___y_2221_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2226_, lean_object* v_s_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_s_boxed_2233_; lean_object* v_res_2234_; 
v_s_boxed_2233_ = lean_unbox(v_s_2227_);
v_res_2234_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_2226_, v_s_boxed_2233_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object* v_env_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_2235_, v___y_2237_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(v_env_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2249_, lean_object* v_bs_2250_, lean_object* v_k_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_2250_, v_k_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2258_, lean_object* v_bs_2259_, lean_object* v_k_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_2258_, v_bs_2259_, v_k_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_bs_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object* v_00_u03b1_2267_, lean_object* v_bs_2268_, lean_object* v_k_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_2268_, v_k_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_bs_2277_, lean_object* v_k_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(v_00_u03b1_2276_, v_bs_2277_, v_k_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2285_, lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_constName_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(v_00_u03b1_2293_, v_constName_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2301_, lean_object* v_msg_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_msg_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(v_00_u03b1_2309_, v_msg_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2317_, lean_object* v_ref_2318_, lean_object* v_constName_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2318_, v_constName_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2326_, lean_object* v_ref_2327_, lean_object* v_constName_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2326_, v_ref_2327_, v_constName_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_ref_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2335_, lean_object* v_ref_2336_, lean_object* v_msg_2337_, lean_object* v_declHint_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2336_, v_msg_2337_, v_declHint_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2345_, lean_object* v_ref_2346_, lean_object* v_msg_2347_, lean_object* v_declHint_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2345_, v_ref_2346_, v_msg_2347_, v_declHint_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v_ref_2346_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2355_, lean_object* v_declHint_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2355_, v_declHint_2356_, v___y_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2363_, lean_object* v_declHint_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2363_, v_declHint_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2371_, lean_object* v_ref_2372_, lean_object* v_msg_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2372_, v_msg_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2380_, lean_object* v_ref_2381_, lean_object* v_msg_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2380_, v_ref_2381_, v_msg_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_ref_2381_);
return v_res_2388_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx);
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
